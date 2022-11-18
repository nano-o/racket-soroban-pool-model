theory AMM
  imports "Word_Lib.Machine_Word_64" HOL.Real
begin

section "Pool state"

record pool_state_spec =
  x :: real
  y :: real
  l :: real

definition k where "k p \<equiv> (x p)*(y p)"

section "Adding liquidity"

definition add_liquidity_spec where
  "add_liquidity_spec p \<Delta>x \<equiv> let \<alpha> = \<Delta>x / (x p)
    in \<lparr>x = ((1+\<alpha>)*(x p)), y = ((1+\<alpha>)*(y p)), l = ((1+\<alpha>)*(l p))\<rparr>"

definition add_liquidity_code where
  "add_liquidity_code p \<Delta>x \<equiv>
    \<lparr>x = ((x p) + \<Delta>x),
     y = ((y p) + \<lfloor>(\<Delta>x*(y p)) / (x p)\<rfloor> + 1),
     l = ((l p) + \<lfloor>(\<Delta>x*(l p)) / (x p)\<rfloor>)\<rparr>"

lemma thm_1:
  \<comment> \<open>properties of add_liquidity\<close>
  fixes p \<Delta>x
  assumes "x p > 0" and "y p > 0" and "l p > 0"
    and "\<Delta>x > 0"
  defines "p' \<equiv> add_liquidity_spec p \<Delta>x"
    and "p'' \<equiv> add_liquidity_code p \<Delta>x"
  shows "x p < x p'" and "x p' = x p''" and "y p < y p'"
    and "y p' < y p''" and "y p'' \<le> y p' + 1"
    and "l p' - 1 < l p''" and "l p'' \<le> l p'"
    and "k p < k p'" and "k p' < k p''"
    and "(k p')/(k p) = ((l p')/(l p))\<^sup>2"
    and "((l p'')/(l p))\<^sup>2 < (k p'')/(k p)"
proof -
  have l1:"(1 + \<Delta>x / x p) * a = a + \<Delta>x * a / x p" for a
    \<comment> \<open>this simple lemma helps automated provers a lot\<close>
    by algebra
  show "x p < x p'"
    by (metis add.commute add_liquidity_spec_def assms(1,4) div_self l1 less_add_same_cancel2 mult.comm_neutral order_less_irrefl p'_def select_convs(1) times_divide_eq_right)
  show "x p' = x p''"
    using assms(1-4) unfolding p'_def p''_def add_liquidity_spec_def add_liquidity_code_def Let_def
    by (auto; metis add_divide_distrib eq_divide_eq_1 nonzero_eq_divide_eq order_less_irrefl)
  show "y p < y p'"
    by (simp add: add_liquidity_spec_def assms(1,2,4) l1 p'_def)
  show "y p' < y p''"
    by (simp add: add_liquidity_code_def add_liquidity_spec_def l1 p''_def p'_def)
  show "y p'' \<le> y p' + 1"
    by (simp add: add_liquidity_code_def add_liquidity_spec_def l1 p''_def p'_def)
  show "l p' - 1 < l p''"
    by (simp add: add_liquidity_code_def add_liquidity_spec_def l1 p''_def p'_def) 
  show "l p'' \<le> l p'"
    by (simp add: add_liquidity_code_def add_liquidity_spec_def l1 p''_def p'_def)
  show "k p < k p'"
    by (simp add: \<open>x p < x p'\<close> \<open>y p < y p'\<close> assms(1,2) k_def less_eq_real_def mult_le_less_imp_less)
  show "k p' < k p''"
    by (metis \<open>x p < x p'\<close> \<open>x p' = x p''\<close> \<open>y p' < y p''\<close> assms(1) dual_order.strict_trans k_def mult.commute mult_less_iff1) 
  show "(k p')/(k p) = ((l p')/(l p))^2"
    using assms(1-4) unfolding p'_def add_liquidity_spec_def Let_def k_def
    by (simp; algebra)
  show "((l p'')/(l p))^2 < (k p'')/(k p)"
  proof -
    have "((l p + \<lfloor>\<Delta>x * l p / x p\<rfloor>) / l p)\<^sup>2 \<le> ((l p + \<Delta>x * l p / x p) / l p)\<^sup>2"
    proof -
      have "((l p + \<lfloor>\<Delta>x * l p / x p\<rfloor>) / l p) \<le> ((l p + \<Delta>x * l p / x p) / l p)"
        by (simp add: assms(3) pos_le_divide_eq)
      thus ?thesis
        using assms(1,3,4) by fastforce
    qed
    moreover
    have "(x p + \<Delta>x) * (y p + \<lfloor>\<Delta>x * y p / x p\<rfloor> + 1) / (x p * y p)
          > (x p + \<Delta>x) * (y p + \<Delta>x * y p / x p) / (x p * y p)"
      by (smt (verit, ccfv_SIG) assms(1,2,4) less_divide_eq_1_pos linordered_comm_semiring_strict_class.comm_mult_strict_left_mono mult_less_cancel_right real_of_int_floor_add_one_gt times_divide_eq_left zero_less_mult_iff)
    ultimately
    show ?thesis
      by (smt (verit, best) \<open>k p' / k p = (l p' / l p)\<^sup>2\<close> \<open>k p' < k p''\<close> add_liquidity_code_def add_liquidity_spec_def assms(1,2) divide_le_cancel k_def l1 p''_def p'_def select_convs(3) split_mult_pos_le)
  qed
qed

end