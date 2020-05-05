theory Chapter3s
  imports Chapter2 "HOL-Algebra.Group_Action"
  
begin
declare [[smt_timeout = 200]]
section\<open>Digression on Groups and Automorphisms\<close>
text \<open>
\begin{hartshorne}
\defn[group]. A \term{group} is a set $G$ together with a binary operation, called multiplication,
written $ab$ such that
\begin{itemize}
\item[G1] (\term{Associativity}) For all $a,b,c\in G, (ab)c = a(bc)$.
\item[G2] There exists an element $1 \in G$ such that $a \cdot 1 = 1 \cdot a = a \cdot 1 = a$ for all $a$.
\item[G3] For each $a \in G$, there exists an element $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = 1$.
\end{itemize}
The element $1$ is called the \term{identity}, or \term{unit}, element. The element $a^{-1}$ is
called the \term{inverse} of $a.$ Note that in general the product $ab$ may be different from $ba.$
However, we say that the group $G$ is \term{abelian,} or \term{commutative,} if
G4 $\forall a, b \in G, ab = ba.$
\end{hartshorne}
\<close>

text \<open>
\begin{hartshorne}
Examples.

1. Let $S$ be any set, and let $G$ be the set of permutations of the set $S.$
A \term{permutation} is a 1–1 mapping of a set $S$ onto $S.$ If $g_1, g_2 \in G$
are two permutations, we define $g_1 g_2 \in G$ to be the permutation obtained by
performing first $g_2$, then $g_1$, i.e., if $x \in S$, then
$$
(g_1g_2)(x) = g_1(g_2(x)).
$$

2. Let $C$ be a configuration, and let $G$ be the set of \term{automorphisms} of $C$,
i.e., the set of those permutations of $C$ which send lines into lines.
Again we define the product $g_1g_2$ of two automorphisms $g_1,g_2$, by performing
$g_2$ first, and then $g_1.$ This group is written $\operatorname{Aut} C$.

\defn [homomorphism] A \term{homomorphism} $\phi: G_1 \to G_2$ of one group to another is a
mapping of the set $G_1$ to the set $G_2$ such that $\phi(ab) = \phi(a) \phi(b)$ for each $a, b \in G_1$.

An \term{isomorphism} of one group with another is a homomorphism which is
1–1 and onto.

\defn [subgroup]  Let $G$ be a group. A subgroup of $G$ is a non-empty subset
$H \subseteq G,$ such that for any $a,b \in H,$ $ab \in H$ and $a^{-1} \in H.$
\end{hartshorne}
 \<close>





subsection\<open>Automorphisms of the real projective plane\<close>
text \<open>\begin{hartshorne}Here we study another important example of the automorphisms of a pro-
jective plane. Recall that the real projective plane is defined as follows: A point
is given by homogeneous coordinates $(x_1 , x_2 , x_3 )$. That is, a triple of real num-
bers, not all zero, and with the convention that $(x_1 , x_2 , x_3)$ and $(\lambda x_1, \lambda x_2, \lambda x_3)$
represent the same point, for any $\lambda \ne 0$, $\lambda \in \Bbb R.$
A \term{line} is the set of points which satisfy an equation of the form

\begin{equation*}
a_1 x_1 + a_2 x_2 + a_3 x_3 = 0,
\end{equation*}

$a_i \in \Bbb R,$ not all zero. \end{hartshorne}\<close>

subsubsection\<open>Brief review of matrices\<close>
text \<open>\begin{hartshorne}
A $n \times n$ \term{matrix} of real numbers is a collection of $n^2$ real numbers, indexed
by two indices, say $i$, $j$, each of which may take values from 1 to $n$. Hence
$A = {a_{11}, a_{12}, \ldots , a_{21}, a_{22}, \ldots , a_{n1}, a_{n2}, \ldots , a_{nn}}.$ The matrix is
usually written in a square:
$$
\begin{pmatrix}
a_{11} & a_{12} & \hdots & a_{1n} \\
a_{21} & a_{22} & \hdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{n1} & a_{n2} & \hdots & a_{nn}
\end{pmatrix}
$$
Here the first subscript determines the row, and the second subscript determines
the column.

The product of two matrices $A = (a_{ij})$ and $B = (b_{ij})$ (both of order $n$) is
defined to be

\begin{equation*}
  A \cdot B = C
\end{equation*}

where $C = (c_{ij})$ and

\begin{equation*}
  c_{ij} = \sum_{k=1}^n a_{ik} b_{kj}.
\end{equation*}

\[
\begin{pmatrix}
a_{i1} & \hdots & a_{in} \\
\end{pmatrix}
\begin{pmatrix}
b_{1j} \\
\vdots \\
b_{nj} \\
\end{pmatrix}
= ( c_{ij} )
\]


\[c_{ij} = a_{i1}b_{1j} + a_{i2}b_{2j} + \hdots  + a_{in}b_{nj}\]

There is also a function \textbf{determinant}, from the set of $n \times n$ matrices to $\mathbb{R}$,
which is characterized by the following two properties:

\textbf{D1} \textit{If A, B are two matrices}

\[ det(A \cdot B) = det A \cdot det B\]

\textbf{D2} \textit{For each $a \in R$, let $C(a) = \ldots $}

Note incidentally that the identity matrix $I = C(1)$ behaves as a multiplicative identity.
One can prove the following facts:
\begin{enumerate}
\item $(A \cdot B) \cdot C = A \cdot (B \cdot C)$, i.e. multiplication of matrices is associative.
(In general it is not commutative.)

\item A matrix $A$ has a multiplicative inverse $A^{-1}$
if and only if $det A \neq 0$.

Hence the set of $n \times n$ matrices $A$ with $\det A \neq 0$ forms a group under multiplication,
denoted by GL$(n, \mathbb{R})$.
\item Let $A = (a_{ij})$ be a matrix, and consider the set of simultaneous linear
equations
\begin{align}
a_{11}x_1 + a_{12}x_2 + \hdots + a_{1n}x_n &= b_1 \\
a_{21}x_1 + a_{22}x_2 + \hdots + a_{2n}x_n &= b_2 \\
\vdots &= \vdots\\
a_{n1}x_1 + a_{n2}x_2 + \hdots + a_{nn}x_n &= b_n
\end{align}
If $\det A \neq 0$, then this set of equations has a solution. Conversely, if this
set of equations has a solution for all possible choices of $b_1, \hdots, b_n$ then
$\det A \neq 0$.
\end{enumerate}
For proofs of these statements, refer to any book on algebra. We will take
them for granted, and use them without comment in the rest of the course. One
can prove easily that 3 follows from 1 and 2. Because to say $x_1, \hdots, x_n$ are a
solution of that system of linear equations is the same as saying that

\[
A \cdot
\begin{pmatrix}
x_1 \\
x_2 \\
\vdots \\
x_n \\
\end{pmatrix}
=
\begin{pmatrix}
b_1 \\
b_2 \\
\vdots \\
b_n \\
\end{pmatrix}
\]
Now let $A = (a_{ij})$ be a $3 \times 3$ matrix of real numbers, and let $\pi$ be the real
projective plane, with homogeneous coordinates $x_1, x_2, x_3$. We define a transformation $T_A$ of $\pi$ as follows:
The point $(x_1, x_2, x_3)$ goes into the point
\[T_A(x_1, x_2, x_3) = (x_1', x_2', x_3')\]
where
\[x_1' = a_{11}x_1 + a_{12}x_2 + a_{13}x_3\]
\[x_2' = a_{21}x_1 + a_{22}x_2 + a_{23}x_3\]
\[x_3' = a_{31}x_1 + a_{32}x_2 + a_{33}x_3\]
\end{hartshorne}
\<close>

(*
CONTINUES WITH DOT-PRODUCT DEFINITION OF MATRIX MULTIPLICATION
*)

(*
(* Proposition 3.1: There is a 1-1 correspondence between the elements
 of H, a subgroup of G, and the elements of gH. *)

(* Some definitions that make the statement of 3.1 easier. *)
definition injective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set)  \<Rightarrow> bool"
  where "injective f U V  \<longleftrightarrow> (\<forall> u1 \<in> U. \<forall> u2 \<in> U. (f(u1) = f(u2)) \<longleftrightarrow> (u1 = u2))"

definition surjective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set) \<Rightarrow> bool"
  where "surjective f U V  \<longleftrightarrow>  (\<forall> v \<in> V. \<exists>u \<in> U. f(u) = v)"

definition bijective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set)  \<Rightarrow> bool"
  where "bijective f U V \<longleftrightarrow> (injective f U V \<and> surjective f U V)"

(* A map is homomorphic if it preserves the structure of the objects it maps between.
 * I.e., if it preserves the behavior of the operators A and B. *)
definition homomorphic :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b  \<Rightarrow> 'b) \<Rightarrow> bool"
  where "homomorphic f A B \<longleftrightarrow> ( \<forall> a b. (f(A a b) = B (f(a)) (f(b))))"
*)


(*
lemma bijection_btw_left_cosets:
  assumes "group G"
  assumes "g \<in> carrier G"
  assumes "subgroup H G"
  assumes "gH = H <#\<^bsub>G\<^esub> g"
  shows "\<exists>f. bij_betw f H gH"
proof -
  have "gH \<in> lcosets\<^bsub>G\<^esub> H" sorry
  thus thesis? sorry
qed
*)

lemma group_action_is_group:
  assumes "group_action G E phi"
  shows "group G"
  using assms group_action.group_hom group_hom.axioms(1) by blast

lemma bij_group_action:
  assumes "G = BijGroup S"
  shows "group_action G S (\<lambda>g e. g(e))"
  by (simp add: assms group_BijGroup group_action.intro group_hom.intro group_hom_axioms.intro homI)

lemma bij_trans_action:
  assumes "G = BijGroup S"
  shows "transitive_action G S (\<lambda>g. g)"
  unfolding transitive_action_def
  apply (intro conjI)
  subgoal
    by (simp add: assms bij_group_action)
  unfolding transitive_action_axioms_def
  subgoal
    apply (intro allI)
    apply (intro impI)
    proof -
      fix x y assume xy: "x \<in> S" "y \<in> S"
      show "\<exists>g\<in>carrier G. g x = y"
      proof -
        let ?f =
         "(\<lambda>z. (if (z \<in> S) then
                       (if (z = x) then y
                        else (if (z = y) then x else z)) else undefined))"
          have f_bij: "bij_betw ?f S S"
            unfolding bij_betw_def
            apply (intro conjI)
            subgoal
              by (simp add: inj_on_def)
            subgoal
            proof
              show "?f ` S \<subseteq> S"
                using xy(1) xy(2) by auto
              show "S \<subseteq> ?f ` S"
                using image_eqI xy(1) xy(2) by auto
            qed
          done
        then have f_ext: "?f \<in> extensional S"
        by (simp add: extensional_def)
        from f_ext f_bij have f_in_G: "?f \<in> carrier G"
        by (simp add: BijGroup_def Bij_def assms)
      have xy_swap: "?f x = y"
        by (simp add: xy(1))
      thus ?thesis using xy_swap f_in_G
        by auto
    qed
  qed
  done



text\<open>Example\<close>
lemma bij_fix_el_are_subgroup:
  assumes "G = BijGroup S"
  assumes "x \<in> S"
  assumes "H = stabilizer G (\<lambda>g e. g(e)) x"
  shows "subgroup H G"
  using assms(1) assms(2) assms(3) bij_group_action group_action.stabilizer_subgroup by fastforce

text\<open>Proposition 3.1 (but with right cosets)\<close>
lemma bij_btw_right_cosets:
  assumes "group G"
  assumes "g \<in> carrier G"
  assumes "subgroup H G"
  assumes "Hg = H #>\<^bsub>G\<^esub> g"
  shows "\<exists>f. bij_betw f H Hg"
proof -
  have "Hg \<in> rcosets\<^bsub>G\<^esub> H"
    by (simp add: assms(1) assms(2) assms(3) assms(4) group.rcosetsI group.subgroupE(1))
  thus ?thesis
    using assms(1) assms(3) group.card_cosets_equal subgroup.subset by blast
qed

text\<open>Corollary 3.2\<close> (* XXX This seems like just group.lagrange; why re-state it? *)
lemma lagrange_card_thm:
  assumes "group G"
  assumes "subgroup H G"
  shows "card(carrier G) = card(H) * card(rcosets\<^bsub>G\<^esub> H)"
  by (metis assms(1) assms(2) group.lagrange order_def semiring_normalization_rules(7))

text\<open>Example\<close>
lemma orbit_stabilizer_thm:
  assumes "G = BijGroup S"
  assumes "phi = (\<lambda>g e. g(e))"
  assumes "x \<in> S"
  assumes "H = stabilizer G phi x"
  shows "card(carrier G) = card(H) * card(orbit G phi x)"
proof -
  have "group_action G S phi"
      by (simp add: assms(1) assms(2) bij_group_action)
    thus ?thesis
      by (metis assms(3) assms(4) group_action.orbit_stabilizer_theorem mult.commute order_def)
qed


text\<open>Example above, in transitive group\<close>
lemma trans_orbit_stabilizer_thm:
  assumes "subgroup G_car (BijGroup S)"
  assumes "G = \<lparr>carrier = G_car, mult = mult (BijGroup S), one = one (BijGroup S)\<rparr>"
  assumes "phi = (\<lambda>g e. g(e))"
  assumes "transitive_action G S phi"
  assumes "x \<in> S"
  assumes "H = stabilizer G phi x"
  shows "card(carrier G) = card(H) * card(S)"
proof -
  have "card(carrier G) = card(H) * card(orbit G phi x)"
    by (metis assms(4) assms(5) assms(6) group_action.orbit_stabilizer_theorem mult.commute order_def transitive_action.axioms(1))
  also have "S = orbit G phi x"
  proof
    show "S \<subseteq> orbit G phi x"
      by (smt CollectI assms(4) assms(5) orbit_def subsetI transitive_action.unique_orbit)
    show "orbit G phi x \<subseteq> S"
      by (smt assms(4) assms(5) group_action.element_image mem_Collect_eq orbit_def subsetI transitive_action.axioms(1))
  qed
  then have cards_same: "card S = card (orbit G phi x)"
    by simp
  thus ?thesis
    by (simp add: calculation)
qed


text\<open>Corollary 3.3\<close>
lemma same_el_one_set:
  assumes "x \<in> S"
  and "\<And>y. y \<in> S \<Longrightarrow> y = x"
  shows "S = {x}"
proof
  show "{x} \<subseteq> S"
    by (simp add: assms(1))
  show "S \<subseteq> {x}"
  proof
    fix z assume "z \<in> S"
    then show "z \<in> {x}"
      by (simp add: \<open>z \<in> S\<close> assms(2))
  qed
qed

lemma base_num_perms:
  assumes "card K = 1"
  assumes "H = BijGroup K"
  shows "card (carrier H) = 1"
proof -
  obtain f g where fg: "f \<in> carrier H" "g \<in> carrier H"
    using assms(2) group.subgroup_self group_BijGroup subgroup_def by blast
  then have fj_bij: "bij_betw f K K" "bij_betw g K K"
      using assms(1) assms(2)
       apply (simp add: BijGroup_def Bij_def)
      by (metis BijGroup_def Bij_def Int_Collect assms(2) fg(2) partial_object.select_convs(1))
  then have "f = (\<lambda>x \<in> K. x)"
      using assms(1) fg BijGroup_def
      by (smt BijGroup_def Bij_imp_extensional Pi_split_insert_domain assms(1) assms(2) bij_betw_imp_funcset card_1_singletonE extensional_restrict fg(1) partial_object.select_convs(1) restrict_ext singletonD)
  then have "f = one H"
      using BijGroup_def
      by (simp add: BijGroup_def assms(2))
  from fg fj_bij have fgeq: "g = f"
      by (smt BijGroup_def Bij_imp_extensional Pi_split_insert_domain assms(1) assms(2) bij_betw_imp_funcset card_1_singletonE extensional_restrict partial_object.select_convs(1) restrict_ext singletonD)
  from fg fgeq have "carrier H = {f}"
      using same_el_one_set
      by (smt BijGroup_def Bij_def Int_Collect Pi_split_insert_domain assms(1) assms(2) bij_betw_imp_funcset card_1_singletonE extensionalityI partial_object.select_convs(1) singletonD)
  then show "card(carrier H) = 1"
      by simp
  qed

(*GOOD PROOF TO TRY: if inverse exists then fun is bijective*)

lemma bij_when_rm_fixed_el:
  assumes "bij_betw f S S"
  assumes "x \<in> S"
  assumes "f(x) = x"
  assumes "S' = S - {x}"
  shows "bij_betw f S' S'"
  by (metis (no_types, lifting) Diff_idemp Diff_insert_absorb assms(1) assms(3) assms(4) bij_betw_def image_insert inj_on_insert insert_Diff)

lemma rm_elt_then_add_sm_fun:
  assumes "card S \<ge> 2"
  assumes "f \<in> (Bij S)"
  assumes "x \<in> S"
  assumes "f(x) = x"
  assumes "S' = S - {x}"
  assumes "g = restrict f S'"
  shows "(\<lambda>y. if y = x then x else g y) = f"
proof
  fix z
  show "(\<lambda>y. if y = x then x else g y) z = f z"
  proof (cases "x = z")
    case True
    then show ?thesis
      using assms(4) Bij_def
      by simp
  next
    case False
    then show ?thesis
      using assms(2) Bij_def
      using Bij_imp_extensional assms(5) assms(6) extensional_arb by fastforce
  qed
qed

lemma add_then_rm_elt_sm_fun:
  assumes "card S \<ge> 2"
  assumes "x \<in> S"
  assumes "S' = S - {x}"
  assumes "f \<in> Bij S'"
  shows "restrict (\<lambda>y. if y = x then x else f y) S' = f"
  by (smt Bij_imp_extensional Diff_insert_absorb assms(2) assms(3) assms(4) extensional_restrict mk_disjoint_insert restrict_ext)

lemma finite_surj_impl_bijection:
  fixes f 
  fixes K
  assumes "f `K = K"
  assumes "Finite_Set.finite K"
  shows "bij_betw f K K"
proof -
  have 1: "finite K" using assms(2) by auto
  have 2: "card(f `K) = card(K)" using assms(1) by auto
  have 3: "inj_on f K" using 1 2 eq_card_imp_inj_on by auto
  thus ?thesis using 3 assms(1)
    by (simp add: bij_betw_def)
qed


lemma induct_num_perms:
  fixes n :: "nat"
  assumes "card S = n + 1 \<Longrightarrow> G = BijGroup S  \<Longrightarrow> card (carrier G) = fact(n + 1)"
  assumes "card K = n + 2"
  assumes "H = BijGroup K"
  shows "card(carrier H) = fact(n + 2)"
proof -
  have H_trans: "transitive_action H K (\<lambda>g. g)"
    by (simp add: assms(3) bij_trans_action)

  obtain x where x: "x \<in> K" using assms(2) by fastforce
  obtain Hx where Hx: "Hx = stabilizer H (\<lambda>g. g) x" by simp

  from H_trans Hx have os: "card (carrier H) = (card K) * (card Hx)"
    using trans_orbit_stabilizer_thm
    by (smt assms(3) group.subgroup_self group_BijGroup monoid.surjective mult.commute old.unit.exhaust x)

  have cd_Hx: "card Hx = fact(n + 1)"
  proof -
    (*Isabelle sees a difference between Hx, a set of permutations on K, and Hx' the set
    of permutations on K - {x}. Since the assumption in the inductive hypothesis requires
    a BijGroup, I can't use Hx. I defined a new BijGroup called Hx' as the set of bijections on
    K - {x}, and am currently proving that there is a bijection between Hx and Hx' (yes,
    they are also isomorphic, but that's a good deal of work for Isabelle. *)
    let ?K' = "K - {x}"
    let ?Hx' = "carrier (BijGroup ?K')"
    let ?phi = "\<lambda>(f ::'b \<Rightarrow>'b). restrict f ?K'"
    have "extensional ?phi"
    let ?phi_inv = "\<lambda>f y. if (y \<notin>  K) then undefined else if y = x then x else f y" (* JFH: Changed this *)
    have hx_bij: "?Hx' = Bij ?K'" by (simp add: BijGroup_def)

    have q1a: "\<lbrakk>u \<in> K; f(x) = x\<rbrakk> \<Longrightarrow>(?phi_inv (?phi f)) u = f u" by simp
    have q1b: "\<lbrakk>u \<in> K; f \<in> Hx\<rbrakk> \<Longrightarrow>(?phi_inv (?phi f)) u = f u"    by (simp add: Hx stabilizer_def)
    have "(?phi_inv g) x = x" by (simp add: x) 
    have q2: "\<lbrakk>u \<in> ?K'\<rbrakk> \<Longrightarrow>(?phi (?phi_inv g)) u = g u" by simp
    have u1: "carrier \<lparr>carrier = Bij K, monoid.mult = \<lambda>g\<in>Bij K. restrict (compose K g) (Bij K), one = \<lambda>x\<in>K. x\<rparr> = Bij K" by auto
    have q2b: "\<lbrakk>g \<in> Hx\<rbrakk> \<Longrightarrow>(restrict (?phi_inv g) K)  \<in> Hx" unfolding Hx stabilizer_def BijGroup_def assms(3) 
    proof -
      have "\<lbrakk>g \<in> Bij K\<rbrakk>  \<Longrightarrow> (\<lambda>y\<in>K. if y \<notin> K then undefined else if y = x then x else g y) \<in> Bij K" 
    proof -
      have ?thesis unfolding Hx stabilizer_def carrier_def partial_object_ext_Tuple_Iso_def id_def Fun.comp_def iso_tuple_fst_def fst_def repr_def Rep_partial_object_ext 
      proof -
        have "(\<lambda>y\<in>K. if y = x
  then x else g y)
    \<in> {g \<in> case rec_tuple_isomorphism
        (\<lambda>r a. r)
        (tuple_isomorphism.Tuple_Isomorphism
Rep_partial_object_ext
Abs_partial_object_ext)
        H of
  (x1, x2) \<Rightarrow> x1.
        g x = x}"  using assms(3) unfolding BijGroup_def 


    (* I proved these claims just to sanity check the correctness of the formations above.
      They also are helpful for proving surjectivity of phi.*)
    have cod_phi_hxp: "\<And>f. \<lbrakk>f \<in> Hx\<rbrakk> \<Longrightarrow> (?phi f) \<in> ?Hx'"
    proof -
      fix f assume f: "f \<in> Hx"
      show "?phi f \<in> ?Hx'"
      proof -
        have "?phi f \<in> Bij ?K'"
          unfolding Bij_def
        proof
          show "(?phi f) \<in> extensional ?K'"
            by simp
          show "(?phi f) \<in> {h. bij_betw h ?K' ?K'}"
          proof
            have bij_res: "bij_betw f ?K' ?K'"
              using bij_when_rm_fixed_el
              by (metis (mono_tags, lifting) BijGroup_def Bij_def Hx Int_Collect assms(3) f mem_Collect_eq partial_object.select_convs(1) stabilizer_def x)
            then show "bij_betw (?phi f) ?K' ?K'"
              using bij_betw_restrict_eq by blast
          qed
        qed
        thus ?thesis
          using hx_bij by simp
      qed
    qed

    have cod_phi_inv_hx: "\<And>f. \<lbrakk>f \<in> ?Hx'\<rbrakk> \<Longrightarrow> (?phi_inv f) \<in> Hx"
    proof -
      fix f assume f: "f \<in> ?Hx'"
      show "?phi_inv f \<in> Hx"
      proof -
        have "f \<in> Bij ?K'"
          using hx_bij f
          by blast
        have "?phi_inv f \<in> stabilizer H (\<lambda>g. g) x"
          unfolding stabilizer_def
        proof
          show "?phi_inv f \<in> carrier H \<and> (?phi_inv f) x = x"
          proof (intro conjI)
            show "(?phi_inv f) x = x"
              by simp
            show "?phi_inv f \<in> carrier H"
            proof -
              have "?phi_inv f \<in> Bij K"
                unfolding Bij_def
              proof
                show "?phi_inv f \<in> extensional K"
                  by (smt Bij_imp_extensional \<open>f \<in> Bij (K - {x})\<close> extensional_def insertCI insert_Diff mem_Collect_eq x)
                show "?phi_inv f \<in> {f. bij_betw f K K}"
                proof
                  have i: "inj_on (?phi_inv f) K"
                    using inj_on_def x f bij_group_action
                    by (smt Diff_insert_absorb group_action.element_image group_action.inj_prop insert_iff mk_disjoint_insert)
                  have s: "(?phi_inv f) ` K = K"
                    sorry (*I'm not too worried about this one*)
                  show "bij_betw (?phi_inv f) K K"
                    using i s bij_betw_def
                    by blast
                qed
              qed
              thus ?thesis
                using BijGroup_def
                by (simp add: BijGroup_def assms(3))
            qed
          qed
        qed
        thus ?thesis
          using Hx by blast
      qed
    qed

    have cd_sm: "card Hx = card ?Hx'"
    proof -
      have "bij_betw ?phi Hx ?Hx'"
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on ?phi Hx"
        proof
          fix a b assume ab: "a \<in> Hx" "b \<in> Hx"
          show "(?phi a) = (?phi b) \<Longrightarrow> a = b"
          proof -
            assume phi_eq: "(?phi a) = (?phi b)"
            have a_inv_a: "a = ?phi_inv (?phi a)"
              using rm_elt_then_add_sm_fun
              sorry (*for one reason or another, sledgehammer/try won't confirm these, even
                     when I provd rm_elt_then_add_sm_fun. But I think this is a solvable
                     once I prove that if a function is invertible <=> bijective. *)
            have b_inv_b: "b = ?phi_inv (?phi b)"
              using rm_elt_then_add_sm_fun hx_bij cod_phi_hxp
              sorry
            then have b_inv_a: "b = ?phi_inv (?phi a)"
              using phi_eq
              by metis
            then show "a = b"
              using a_inv_a b_inv_a
              by simp
          qed
        qed
        show "?phi ` Hx = ?Hx'"
        proof
          show "?phi ` Hx \<subseteq> ?Hx'"
            using cod_phi_hxp by blast
          show "?Hx' \<subseteq> ?phi ` Hx"
          proof
            fix g assume g: "g \<in> ?Hx'"
            have "g \<in> Bij ?K'"
              using hx_bij g by blast
            show "g \<in> ?phi ` Hx"
              unfolding image_def
            proof
              let ?g' = "?phi_inv g"
              have g'_in_hx: "?g' \<in> Hx"
                using cod_phi_inv_hx g by blast
              then have g_back: "g = ?phi ?g'"
                using add_then_rm_elt_sm_fun
                by (metis (no_types, lifting) \<open>g \<in> Bij (K - {x})\<close> add_diff_cancel_left' assms(2) diff_le_self restrict_ext x)
              show "\<exists>g' \<in> Hx. g = ?phi g'"
                using g'_in_hx g_back
                by auto
            qed
          qed
        qed
      qed
      thus ?thesis
        using bij_betw_same_card by blast
    qed
    have "card (K - {x}) = n + 1"
      using assms(2)
      by (metis One_nat_def Suc_eq_plus1 add_Suc_shift add_diff_cancel_right' card.infinite card_Diff_singleton nat.simps(3) numeral_2_eq_2 x)

    (* this is the where I'm having trouble. I'd think that this would easily go through because
    I assume the inductive hypothesis at the beginning of the lemma, but try/sledgehammer
    can't seem to confirm it*)
    have induct: "card ?Hx' = fact(n + 1)"
      using assms(1)
      sorry
    thus ?thesis
      using cd_sm
      by simp
  qed
e
  from os cd_Hx have "card (carrier H) = (n + 2) * fact(n + 1)"
    by (simp add: assms(2))
  thus ?thesis
    by simp
qed


corollary num_perms:
  fixes n :: "nat"
  assumes "G = BijGroup S"
  shows "card S = (n + 1) \<Longrightarrow> card (carrier G) = fact(n + 1)"
  apply (induction n)
  subgoal using base_num_perms
    by (simp add: base_num_perms assms)
  subgoal using induct_num_perms
    by (metis Suc_eq_plus1 add_2_eq_Suc' assms)
  done

end
