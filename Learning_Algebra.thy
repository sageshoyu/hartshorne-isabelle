theory Learning_Algebra
  imports Complex_Main "HOL-Algebra.Sym_Groups"

begin
declare [[smt_timeout = 300]]


locale single_elt_group =
  fixes e :: "'a"
  fixes binop:: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "+++" 70)
  assumes "e +++ e = e"

begin
definition one_group :: "'a monoid"
  where "one_group = \<lparr>carrier = {e}, mult = (+++), one = e\<rparr>"

lemma one_group_closed: "\<And>x y. \<lbrakk>x \<in> carrier one_group; y \<in> carrier one_group \<rbrakk> 
  \<Longrightarrow> (x +++ y) \<in> carrier one_group"
proof -
  fix x y
  assume in_group: "x \<in> carrier one_group" "y \<in> carrier one_group"
  from in_group have is_e: "x = e" "y = e" 
    using one_group_def apply auto[1]
    using in_group(2) one_group_def by auto
  have prod_is_e: "x +++ y = e" 
    by (metis is_e(1) is_e(2) single_elt_group_axioms single_elt_group_def)
  from prod_is_e show "(x +++ y) \<in> carrier one_group"
    using in_group(1) is_e(1) by auto
qed

lemma e_is_id:
  assumes "g \<in> carrier one_group"
  shows "g +++ e = g" "e +++ g = g"
proof -
  have g: "g = e"
    using assms one_group_def by auto
  from g show "g +++ e = g" "e +++ g = g"
    apply (meson single_elt_group_axioms single_elt_group_def)  
    by (metis g single_elt_group_axioms single_elt_group_def)
qed

lemma binop_is_assoc:
  assumes "x \<in> carrier one_group"
  assumes "y \<in> carrier one_group"
  assumes "z \<in> carrier one_group"
  shows "(x +++ y) +++ z = x +++ (y +++ z)"
  using assms(1) assms(2) assms(3) e_is_id(1) one_group_def by auto


lemma inverses_exist:
  assumes "x \<in> carrier one_group"
  shows "\<exists> y \<in> carrier one_group. y +++ x = e"
  using assms e_is_id(2) one_group_def by auto

theorem sym_group_is_group: "group one_group"
  unfolding group_def
  unfolding monoid_def
  apply (intro conjI)
  subgoal using one_group_closed
    by (simp add: one_group_def)
  subgoal using binop_is_assoc
    by (simp add: one_group_def)
  subgoal by (simp add: one_group_def)
  subgoal using inverses_exist
    by (simp add: one_group_def)
  subgoal using e_is_id
    by (simp add: one_group_def)
  unfolding group_axioms_def
  by (simp add: Units_def e_is_id(1) one_group_def)  
end

lemma (in single_elt_group) sub_group_is_one_group:
  assumes "subgroup H one_group"
  shows "H = carrier one_group"
  using assms one_group_def subgroup.one_closed subgroup.subset by fastforce

lemma (in single_elt_group) coset_are_one_group:
  assumes "subgroup H one_group"
  assumes "g \<in> carrier one_group"
  shows "g <#\<^bsub>one_group\<^esub> H = carrier one_group"
  using assms(1) assms(2) group.coset_join3 local.sym_group_is_group single_elt_group.sub_group_is_one_group single_elt_group_axioms by fastforce

end