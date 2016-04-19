#include <stdlib.h>
#include "exec-all.h"
#include "tcg-op.h"
#include "helper.h"
#define GEN_HELPER 1
#include "helper.h"
#include "optimization.h"

extern uint8_t *optimization_ret_addr;

/*
 * Shadow Stack
 */
list_t *shadow_hash_list;

static inline void shack_init(CPUState *env) {
	env->shack = (uint64_t *)malloc(SHACK_SIZE * sizeof (uint64_t));
	env->shack_top = env->shack;
	env->shack_end = env->shack + SHACK_SIZE;
	env->shadow_hash_list = (void *)malloc(TB_JMP_CACHE_SIZE * sizeof (list_t));
	env->shadow_ret_count = 0;
	env->shadow_ret_addr = (unsigned long *)malloc(SHACK_SIZE * sizeof (unsigned long));
}

/*
 * shack_set_shadow()
 *  Insert a guest eip to host eip pair if it is not yet created.
 */
inline void shack_set_shadow(CPUState *env, target_ulong guest_eip, unsigned long *host_eip) {
	// move list_it ptr to the guest epi position on the shadow hash list
	list_t *list_it = ((list_t *)env->shadow_hash_list) + tb_jmp_cache_hash_func(guest_eip);
	list_it = list_it->next;
	// check every pair on list_it and assign its corresponding host_eip
	while (list_it) {
		struct shadow_pair *sp = (struct shadow_pair *)list_it;
		if (sp->guest_eip == guest_eip) {
			*sp->shadow_slot = (unsigned long)host_eip;
			return;
		}
		list_it = list_it->next;
	}
}

/*
 * helper_shack_flush()
 *  Reset shadow stack.
 */
void helper_shack_flush(CPUState *env) {
}

/*
 * push_shack()
 *  Push next guest eip into shadow stack.
 */
void push_shack(CPUState *env, TCGv_ptr cpu_env, target_ulong next_eip) {
	//push guest ret address
	TCGv_ptr temp_shack_top = tcg_temp_local_new_ptr();
	TCGv_ptr temp_shack_end = tcg_temp_local_new_ptr();
	int new_label = gen_new_label(); // set the new TCG label with newly assigned numb

	tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
	tcg_gen_ld_ptr(temp_shack_end, cpu_env, offsetof(CPUState, shack_end));
	tcg_gen_addi_ptr(temp_shack_top, temp_shack_top, sizeof (uint64_t));
	tcg_gen_brcond_tl(TCG_COND_LT, temp_shack_top, temp_shack_end, new_label);
	gen_set_label(new_label); // bind new label to op context
	tcg_gen_mov_tl(temp_shack_top, tcg_const_tl((int32_t)(env->shack + 1)));
	tcg_gen_st_tl(tcg_const_tl(next_eip), temp_shack_top, 0); //guest to stack
	tcg_gen_st_tl(tcg_const_tl((int32_t)(env->shadow_ret_addr + env->shadow_ret_count)), temp_shack_top, sizeof (target_ulong)); // tpc to stack
	tcg_gen_st_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));

	tcg_temp_free_ptr(temp_shack_top);
	tcg_temp_free_ptr(temp_shack_end);

	//push host ret address
	TranslationBlock *tb;
	tb_page_addr_t phys_pc = get_page_addr_code(env, next_eip);
	unsigned int h = tb_phys_hash_func(phys_pc);
	TranslationBlock **ptb1 = &tb_phys_hash[h];
	for (;;) {
		tb = *ptb1;
		// assign old shadow as new next
		if (!tb) {
			list_t *old_list = ((list_t *)env->shadow_hash_list) + tb_jmp_cache_hash_func(next_eip);
			struct shadow_pair *new_pair = (struct shadow_pair *)malloc(sizeof (struct shadow_pair));
			new_pair->guest_eip = next_eip;
			new_pair->shadow_slot = env->shadow_ret_addr + env->shadow_ret_count;
			new_pair->l.next = old_list->next;
			old_list->next = &new_pair->l;
			break;
		}
		// tb exist and same as next eip simply assign tb->tc_ptr to host return address
		if (tb->pc == next_eip) {
			*(env->shadow_ret_addr + env->shadow_ret_count) = (unsigned long)tb->tc_ptr;
			break;
		}
		ptb1 = &tb->phys_hash_next;
	}
	env->shadow_ret_count++;
}

/*
 * pop_shack()
 *  Pop next host eip from shadow stack.
 */
void pop_shack(TCGv_ptr cpu_env, TCGv next_eip) {
	TCGv_ptr temp_shack_top = tcg_temp_local_new_ptr();
	TCGv guest_eip = tcg_temp_local_new();
	TCGv host_eip_addr = tcg_temp_local_new();
	TCGv host_eip = tcg_temp_local_new();
	int temp_label = gen_new_label();
	
	tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
	tcg_gen_ld_tl(guest_eip, temp_shack_top, 0);
	tcg_gen_brcond_tl(TCG_COND_NE, next_eip, guest_eip, temp_label);
	tcg_gen_ld_tl(host_eip_addr, temp_shack_top, sizeof (target_ulong));
	tcg_gen_ld_tl(host_eip, host_eip_addr, 0);
	tcg_gen_subi_tl(temp_shack_top, temp_shack_top, 2 * sizeof (target_ulong));
	tcg_gen_st_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
	tcg_gen_brcond_tl(TCG_COND_EQ, host_eip, tcg_const_tl(0), temp_label);
	// move to shadow stack
	*gen_opc_ptr++ = INDEX_op_jmp;
	*gen_opparam_ptr++ = GET_TCGV_PTR(host_eip);

	gen_set_label(temp_label);
	tcg_temp_free_ptr(temp_shack_top);
	tcg_temp_free(guest_eip);
	tcg_temp_free(host_eip);
	tcg_temp_free(host_eip_addr);
}

/*
 * Indirect Branch Target Cache
 */
__thread int update_ibtc;
struct ibtc_table *ibtc_tbl;

/*
 * helper_lookup_ibtc()
 *  Look up IBTC. Return next host eip if cache hit or
 *  back-to-dispatcher stub address if cache miss.
 */
void *helper_lookup_ibtc(target_ulong guest_eip) {
	int h = guest_eip & IBTC_CACHE_MASK;
	if (ibtc_tbl->htable[h].guest_eip == guest_eip) {
		return ibtc_tbl->htable[h].tb->tc_ptr;
	}

	update_ibtc = 1;

	return optimization_ret_addr;
}

/*
 * update_ibtc_entry()
 *  Populate eip and tb pair in IBTC entry.
 */
void update_ibtc_entry(TranslationBlock *tb) {
	update_ibtc = 0;
	int h = tb->pc & IBTC_CACHE_MASK;
	ibtc_tbl->htable[h].guest_eip = tb->pc;
	ibtc_tbl->htable[h].tb = tb;
}

/*
 * ibtc_init()
 *  Create and initialize indirect branch target cache.
 */
static inline void ibtc_init(CPUState *env) {
	ibtc_tbl = (struct ibtc_table*)malloc(sizeof(struct ibtc_table));
	memset(ibtc_tbl, 0, sizeof(struct ibtc_table));
}

/*
 * init_optimizations()
 *  Initialize optimization subsystem.
 */
int init_optimizations(CPUState *env) {
	shack_init(env);
	ibtc_init(env);
	return 0;
}

/*
 * vim: ts=8 sts=4 sw=4 expandtab
 */