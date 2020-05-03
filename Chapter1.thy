(* Things left to do in Chapter 1:
  ** Prove that the completion of an affine plane is a projective plane. 
  ** do the "problems" from the back of the book about the cardinality of lines in 
     an affine plane, or a projective plane, etc. --- basically the first five or six
     problems from the back of the book. 
*)

chapter \<open>Introduction: Affine Planes and Projective Planes\<close>
text \<open>
\begin{hartshorne}
Projective geometry is concerned with properties of incidence --- properties which are 
invariant under stretching, translation, or rotation of the plane. Thus in the axiomatic 
development of the theory, the notions of distance and angle will play no part.
However, one of the most important examples of the theory is the real projective plane,
and there we will use all the techniques available (e.g. those of Euclidean geometry and analytic 
geometry) to see what is true and what is not true.
\end{hartshorne}\<close>

section \<open>Affine geometry\<close>
text\<open>
\begin{hartshorne}
Let us start with some of the most elementary facts of ordinary plane geometry, which we will
take as axioms for our synthetic development.

Definition. An \emph{affine plane} is a set, whose elements are called points, and a set of
subsets, called \emph{lines}, satisfying the following three axioms, A1–A3. We will use the
terminology ``$P$ lies on $l$'' or ``$l$ passes through $P$'' to mean the point $P$ is an 
element of the line $l.$
\begin{itemize}
\item{A1.}
 Given two distinct points $P$ and $Q$, there is one and only one line containing both $P$ and $Q.$
We say that two lines are parallel if they are equal or if they have no points in common.\\
\item{A2.}
Given a line $l$ and a point $P$ not on $l,$ there is one and only one line 
$m$ which is parallel to $l$ and which passes through $P.$\\

\item{A3.} There exist three non-collinear points. (A set of points $P_1, \ldots, P_n$ is said to be 
\emph{collinear} if there exists a line $l$ containing them all.)
\end{itemize}

Notation: 
\begin{align}
P \ne Q && \text{$P$ is not equal to $Q$.} \\
P \in l && \text{$P$ lies on $l$.}\\
l \cap m && \text{the intersection of $l$ and $m$.}\\
l \parallel m && \text{$l$ is parallel to  $m$.}\\
\forall && \text{for all.}\\
\exists && \text{there exists.}\\
\implies && \text{implies.}
\iff && \text{if and only if.}
\end{align}
\end{hartshorne}
\<close>
text \<open>
\spike
To translate to Isabelle, we are saying that to have an affine plane, you need two types (which are
how we choose to represent
sets in Isabelle), and a relationship between them. The statement "meets P l" indicates the notion
that the "point" P lies on the "line" l. For Hartshorne, we would say P is an element of l, but using
point sets as lines turns out to be a horrible idea in Isabelle, so we just deal with `meets.' 
\<close>
text \<open>
We've based our theory on "Complex\_Main" instead of main so that we have the datatype "real". To 
characterize affine and projective planes (the main topics of study) we use ``locales'', an Isabelle 
construct that lets us say ``this entity satisfies this collection of defining axioms.'' The declaration
about ``smt\_timeout'' lets one of the solvers we use have extra time in which to 
discover or confirm correctness of proofs. \done
\<close>
theory Chapter1
  imports Complex_Main

begin
declare [[smt_timeout = 240]]

locale affine_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and meets :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
begin

  fun parallel :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "||" 50) where
  "l || m = (if (l \<in> Lines \<and> m \<in> Lines) 
  then l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m) else l = m)"

fun collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> meets A l \<and> meets B l \<and> meets C l) else False)"
end
  locale affine_plane =
    affine_plane_data  +
  assumes
    a1: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> \<exists>!l. l \<in> Lines \<and> meets P l \<and> meets Q l" and
    a2: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists>!m. m \<in> Lines \<and> l || m \<and> meets P m" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"

begin

text \<open>
\begin{hartshorne}
Example. The ordinary plane, known to us from Euclidean geometry, satisfies the axioms A1–A3, and 
therefore is an affine plane. [NB: We'll return to this below. -- jfh]

A convenient way of representing this plane is by introducing Cartesian coordinates, 
as in analytic geometry. Thus a point $P$ is represented as a pair $(x, y)$ of real numbers. 
(We write $x, y \in \Bbb R$.)

[Omitted picture]
\prop[1.1] Parallelism is an equivalence relation.

\end{hartshorne}
\<close>

  text \<open>
\begin{hartshorne}
\defn[equivalence relation] A relation $\sim$ is an equivalence relation if it has the following
three properties:
\begin{enumerate}
\item Reflexive: $a \sim a$
\item Symmetric: $a \sim b \implies b \sim a$
\item Transitive: $a \sim b$ and $b \sim c \implies a \sim c$.
\end{enumerate}

\proof (of proposition)
We must check the three properties:
1. Any line is parallel to itself, by definition. 

2. $l \parallel m \implies m \parallel l$ by definition.

3. If $l \parallel m$, and $m \parallel n$, we wish to prove $l \parallel n.$

If $l=n$ ,there is nothing to prove.If $l \ne n$,and there is a point
$P \in l \cap n$,then $l, n$ are both $\parallel m$ and pass through $P$, which is impossible by 
axiom A2. We conclude that $l \cap n = \emptyset$ (the empty set), and so $l \parallel n.$
\end{hartshorne}
\<close>

text \<open>
\spike
We now move on to prove some of the elementary claims in the text above, albeit slightly out of 
order. 
\done\<close>

lemma symmetric_parallel: "l || m \<Longrightarrow> m || l"
  by (metis parallel.simps)

text \<open>
\spike
Here's the original proof of that theorem; apparently practice makes perfect (or at least it
shortens things a good deal:
\begin{lstlisting}[language=Isabelle]{}
proof 
    fix l :: "'line" and m :: "'line"
    assume one_direction: "l || m"
    show "m || l"
    proof 
      have "(l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))" 
        using one_direction parallel_def by auto
      from this have "(m = l \<or> \<not> (\<exists> P. meets P m  \<and> meets P l))"
        by auto
      thus "m || l"
        by (simp add: parallel_def)
    qed
  qed
\end{lstlisting}
\done\<close>


lemma reflexive_parallel: "l || l"
  by simp    
(*
  proof - 
    have "l = l" 
      by auto
    thus "l || l"
      using parallel_def by auto
  qed
*)

lemma transitive_parallel: "\<lbrakk>l || m; m || n\<rbrakk> \<Longrightarrow> l || n" 
proof -
  fix l and m and n 
  assume lm: "l || m"
  assume mn: "m || n"
  show "l || n"
  proof -
    have or1: "(l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m))" 
      by (meson lm parallel.elims(2))
    have or2: "(m = n \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P m \<and> meets P n))"
      by (meson mn parallel.elims(2))
    show "l || n"
    proof (cases "l = m")
      case True
      show "l || n"
    
      proof (cases "m = n")
        case True
        then show ?thesis 
          using lm by blast
      next
        case False
        have not_exists1: "\<not> (\<exists> P. P \<in> Points \<and> meets P m \<and> meets P n)"
          using False or2 by blast
        then show ?thesis 
          using True mn by blast
      qed
    next
      case False
      have not_exists2: "\<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m)" 
        using False or1 by blast
      show "l || n"
      proof (cases "m = n")
        case True
        then show ?thesis 
          using lm by blast
      next
        case False
        have not_exists3: "\<not> (\<exists> P. P \<in> Points \<and> meets P m \<and> meets P n)"
          using False or2 by blast
        then show ?thesis
          by (smt a2 lm mn parallel.simps) 
      qed
    qed
    qed
  qed
   
(*
  proof - 
    fix l :: "'line" and m :: "'line" and n :: "'line"
    assume lm: "l || m"
    assume mn: "m || n"
    show "l || n"
    proof -
      have "(l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))"
        using lm parallel_def by blast
      have "(m = n \<or> \<not> (\<exists> P. meets P m  \<and> meets P n))" 
        using mn parallel_def by blast
      thus "l || n"
        by (metis a2 lm parallel_def)
    qed
  qed
*)
  text \<open>\daniel\haoze Equivalence relations can be proved using the following structure with
exported rules.\<close>
lemma equivp_parallel: "equivp parallel"
proof (rule equivpI)
  show "reflp parallel"
    by (simp add: reflexive_parallel reflpI)
  show "symp parallel"
    using symmetric_parallel sympI by blast
  show "transp parallel"
    using transitive_parallel transpI by blast
qed
  text \<open>\done\<close>
end

text  \<open>\spike To help Isabelle along, we insert a tiny theorem giving a different 
characterization of parallelism. \done\<close>

theorem (in affine_plane_data) parallel_alt:
  fixes l
  fixes m
  assumes "l \<noteq> m"
  assumes "l \<in> Lines \<and> m \<in> Lines"
  assumes "\<forall>P. (\<not>meets P l) \<or> (\<not> meets P m)"
  shows "l || m"
proof -
  have "\<not> (\<exists> P. meets P l \<and> meets P m)"
    using assms(3) by blast
  thus "l || m"
    using assms(2) by auto
qed

text  \<open>\begin{hartshorne}
\prop[1.2] Two distinct lines have at most one point in common.

\proof For if $l, m$ both pass through two distinct points $P, Q,$ then by axiom A1, $l = m.$ \endproof

Example. An affine plane has at least four points. There is an affine plane with four points.

Indeed, by A3 there are three non-collinear points. Call them $P, Q, R.$ By A2 there is a line 
$l$ through $P,$ parallel to the line $QR$ joining $Q$ and $R,$ which exists by A1. 
Similarly, there is a line $m \parallel  PQ$, passing through $R.$

Now $l$ is not parallel to $m$ ($l \nparallel m$). For if it were, then we would have 
$PQ \parallel m \parallel l \parallel QR$
and hence $PQ \parallel QR$ by Proposition 1.1. This is impossible, however, because $P Q \ne QR$, 
and both contain $Q.$

Hence $l$ must meet $m$ in some point $S.$ Since $S$ lies on $m,$ which is parallel to $PQ$, and 
different from $PQ,$ $S$ does not lie on $PQ,$ so $S\ne P$,and $S \ne Q$ .Similarly $S \ne R$. Thus
$S$ is indeed a fourth point. This proves the first assertion.

Now consider the lines $PR$ and $QS$. It
may happen that they meet (for example in the real projective plane they will (proof?)). 
On the other hand, it is consistent with the axioms to assume that they do not meet.
In that case we have an affine plane consisting of four points $P, Q, R, S$ and six lines 
$PQ, PR, PS, QR, QS, RS,$ and one can verify easily that the axioms A1–A3 are satisfied. 
This is the smallest affine plane. [NB: We'll return to this final claim presently.]

\end{hartshorne}
\<close>

  (* Two lines meet in at most one point *)
lemma (in affine_plane) prop1P2: "\<lbrakk>l \<noteq> m; meets P l; meets P m; meets Q l; meets Q m; 
l \<in> Lines; m \<in> Lines; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> P = Q"
    using a1 by auto




  



text \<open>\daniel
We can also prove some basic theorems about affine planes not in Hartshorne. The first is that every
point lies on some line; the second is that every line contains at least one point. \done\<close>
  (* Examples of some easy theorems about affine planes, not mentioned in Hartshorne *)
  (* Every point lies on some line *)
  lemma (in affine_plane) containing_line: "\<forall>S \<in> Points. \<exists>l. l \<in> Lines \<and> meets S l"
    by (metis a1 a3)

  (* Every line contains at least one point *)
  lemma (in affine_plane) contained_point: "\<forall>l \<in> Lines. \<exists>S. S \<in> Points \<and> meets S l"
    using a1 a2 a3 parallel.simps collinear.elims by metis


  text \<open>\daniel We enlarge on these to show that every line contains at least \emph{two} points;
we could also show (but don't) that every point lies on at least two lines.\<close>

lemma (in affine_plane) contained_points:
  fixes l
  assumes lline: "l \<in> Lines"
  shows "\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S\<noteq>T \<and> meets S l \<and> meets T l"
proof (rule ccontr)
    assume a: "\<not>(\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S\<noteq>T \<and> meets S l \<and> meets T l)"
    obtain S where S: "S \<in> Points \<and> meets S l"
      using contained_point 
      using lline by auto
    obtain Q where Q: "Q \<in> Points \<and> Q \<noteq> S"
      using a3 by auto
    obtain line where line_def: "meets Q line \<and> meets S line \<and> line \<in> Lines"
      using Q S a1 by blast
    obtain Z where Z: "\<not> meets Z line \<and> Z \<in> Points"
      using a3 line_def by fastforce
    obtain lineprime where lineprime_def: "lineprime \<in> Lines \<and> meets Z lineprime \<and> line || lineprime"
      using Z a2 line_def by blast
    have parallel1: "l || lineprime" 
      using S Z a line_def lineprime_def lline by force
    have par2: "l || lineprime \<and> line || lineprime"
      using lineprime_def parallel1 by blast
    have not_eq: "l \<noteq> line"
      using Q S a line_def by blast
    have False
      by (meson S affine_plane.symmetric_parallel affine_plane.transitive_parallel affine_plane_axioms line_def not_eq par2 parallel.elims(2)) 
    thus "\<not> (\<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S\<noteq>T \<and> meets S l \<and> meets T l) \<Longrightarrow> False"
      by simp
  qed

lemma (in affine_plane) all_contained_points: "\<forall>l \<in> Lines. \<exists> S T. S \<in> Points \<and> T \<in> Points \<and>  S\<noteq>T \<and> meets S l \<and> meets T l"
  using contained_points by auto

  text \<open>\done\<close>

  section  \<open>The real affine plane\<close>
  text \<open> Hartshorne mentioned, just after the definition of an affine plane and some notational 
notes, that the ordinary affine plane is an example of an affine plane. We should prove 
that it's actually an affine plane. It's pretty clear how to represent points --- pairs of real 
numbers --- but what about lines? A line is the set of points satisfying an equation of 
the form Ax + By + C = 0, with not both of A and B being zero. The problem is that there's 
no datatype for ``pair of real numbers, at least one of which is nonzero''. We'll have 
to hack this by breaking lines into ``ordinary'' and ``vertical'', alas.   \<close>

  datatype a2pt = A2Point "real" "real"

  datatype a2ln = A2Ordinary "real" "real" 
                | A2Vertical "real"
  text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `meets' operation for this purported plane, using cases for the definition."

  fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
    "a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
    "a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"

  definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
      where "l a2|| m \<longleftrightarrow> (l = m \<or>  (\<forall> P. (\<not> a2meets P l)  \<or> (\<not>a2meets P m)))"
  text\<open> Notice that I've written the definition of parallel for the euclidean affine plane
as a forall rather than exists. I think this might make things easier.\<close>
  text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>
  text\<open> I'm going to venture into a new style of writing theorems and proofs, one that's
particularly applicable when you're showing something exists by constructing it. Here is 
an example in the case of real numbers: if $r < s$, then there's a real number strictly between
them. We could write this as ``$r < s$ shows that there is a $t$ . ($(r < t)$ and $(t < s)$)'' (although it turns out we'd have
to start with ``\texttt{(r::real) < s ...}'' to tell Isar not to assume that r is a natural number -- after all, 
this is one of those cases where type-inference has no idea whether ``$<$'' means less-than on the reals,
or the integers, or the natural numbers, or ...)

Anyhow, in this new style, we would type the theorem like this:

\begin{lstlisting}[language=Isabelle]{}
theorem mid:
  fixes r :: real
  assumes lt : "r < s"
  shows "\<exists>t. r < t \<and> t < s"
proof
  let ?t = "(r + s) / 2"
  from lt show "r < ?t \<and> ?t < s" by simp
qed
\end{lstlisting}
\<close>

  text\<open>The nice thing about this style is that it takes care of "fix"ing things in the theorem statement,
and takes care of assuming the antecedent (which we always end up doing in the proof anyhow), and
then makes clear what we're going to actually show. We will treat this as a pattern henceforth.

A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result. \caleb \<close>

theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q"
  shows "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
proof (cases P, cases Q)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
  show ?thesis
  proof (cases "(x0 = x1)")

    case True (* Case where x0 = x1 *)
    let ?ll = "A2Vertical x0"
    have m1:  "a2meets P ?ll" using P by simp
    have m2:  "a2meets Q ?ll" using Q True by simp
    have "a2meets P ?ll \<and> a2meets Q ?ll" using m1 m2 by auto
    thus ?thesis by auto
  
  next
    case False (* Case where x0 \<noteq> x1*) 
    let ?rise = "y1 - y0"
    let ?run  = "x1 - x0"
    let ?m    = "?rise/?run"
    let ?b    = "y0 - ?m*x0"
    let ?ll   = "A2Ordinary ?m ?b"

    have m3: "a2meets P ?ll" using P by simp
    have m4: "a2meets Q ?ll"
    proof -
      have s0: "y1*?run/?run = ?m*x1 + (y0 * ?run/?run - ?m*x0)"
        by argo
      have s1: "y1 = ?m*x1 + ?b" using s0 False by auto
      thus ?thesis using s1 Q a2meets.simps(1) by blast

    qed
    show ?thesis using m3 m4 by blast
  qed
qed


text\<open>\done For this next theorem, it might make sense to phrase it as "P notequal Q lets us derive a unique
line l such that..."
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 

This is arguably the ugliest theorem in the bunch, because it involves four cases (one each for 
l and m being ordinary or vertical). Once again, we start by providing names for the constructor
arguments for P and Q:
 \seiji\<close>

lemma A2_a1b: 
  fixes P :: a2pt
  fixes Q
  fixes l
  fixes m
  assumes pq: "P \<noteq> Q"
  assumes pl : "a2meets P l"
  assumes ql : "a2meets Q l"
  assumes pm : "a2meets P m"
  assumes qm : "a2meets Q m"
  shows "l = m"

proof (cases P, cases Q)
    fix x0 y0 assume P: "P = (A2Point x0 y0)"
    fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
    show ?thesis
    proof (cases "(x0 = x1)")
      case True
      then show ?thesis 
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) pl pm pq ql qm)
    next
      case False
      then show ?thesis
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) a2pt.inject crossproduct_noteq pl pm ql qm)
    qed
  qed


lemma A2_a1:
  fixes P :: a2pt
  fixes Q
  assumes pq: "P \<noteq> Q"
  shows "\<exists>! ls . a2meets P ls \<and> a2meets Q ls"
proof -
  show ?thesis using pq A2_a1a A2_a1b by auto
qed

text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction. \caleb\<close>
lemma A2_a2a (*existence*):
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> a2meets P l"
  shows  "\<exists>k. a2meets P k \<and> l a2|| k"

proof (cases P)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  have existence: "\<exists>m. l a2|| m \<and> a2meets P m"
  proof (cases l)
    case (A2Vertical x1)
    obtain m where mvert: "m = (A2Vertical x0)" 
      by simp
    have lparallelm: "a2parallel l m"
      by (metis A2Vertical a2meets.simps(2) a2parallel_def a2pt.exhaust mvert)
    have Ponm: "a2meets P m"
      by (simp add: P mvert)
    then show ?thesis
      using lparallelm by auto
  next
    case (A2Ordinary slope intercept)
    obtain intercept2 where a: "intercept2 = y0 - slope * x0" 
      by simp
    obtain line2 where eq: "line2 = (A2Ordinary slope intercept2)" 
      by simp
    have PonLine2: "a2meets P line2"
      by (simp add: P a eq)
    then show ?thesis
      by (smt A2Ordinary a2meets.elims(2) a2meets.simps(1) a2parallel_def eq) 
  qed
  thus ?thesis
    by auto 
qed

text \<open> \spike At this point, I went down a rabbit hole searching for proofs of the other half

of axiom 2, and kept getting into trouble when dealing with the (pretty simple) algebra 
of straight lines. So I backed off and proved a bunch of small lemmas, partly as practice 
at proving things, and partly to give Isabelle a helping hand when it came to more complicated
things. So here are proofs of things like "a vertical and ordinary line cannot be parallel; if two 
ordinary lines have different slopes, then they intersect; if two vertical lines intersect, they're 
the same; if two ordinary lines with the same slope intersect, then they're the same; if two
ordinary lines are parallel and intersect, then they're the same. \done \<close>

text\<open> Let's start with something dead simple: the other form of parallelism: if 
there's no P meeting both l and m, then they're parallel. \caleb\<close>

lemma A2_parallel_0: 
  fixes l
  fixes m
  fixes P
  assumes nomeet: "\<not> (\<exists>P . a2meets P l \<and> a2meets P m)"
  shows "l a2|| m"

  using a2parallel_def nomeet by auto


text \<open>\done a vertical and ordinary line cannot be parallel \caleb \<close>
lemma A2_basics_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x"
  assumes mo: "m = A2Ordinary s b "
  shows lm_noparr : "\<not> (l a2|| m)"
proof -

  obtain P where P: "P = (A2Point x (x * s + b)) \<and> a2meets P m"
    using mo by force
  have "a2meets P l"
    by (simp add: P lo)
  thus ?thesis
    using P a2parallel_def lo mo by blast

qed

text \<open>\done if two ordinary lines have different slopes, then they intersect \caleb \<close>
lemma A2_basics_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1"
  assumes mo: "m = A2Ordinary s2 b2"
  assumes sdiff: "s1 \<noteq> s2"
  shows lm_noparr2 : "\<not> (l a2|| m)"
proof - 
  obtain x where x: "x = (b2 - b1) / (s1 - s2)"
    by simp
  obtain y where y: "y = s1 * x + b1"
    by simp
  obtain P where P: "P = (A2Point x y)"
    by simp
  have pl: "a2meets P l"
    by (simp add: P lo y)
  have eq1: "s1 * x + b1 = s1 * (b2 - b1) / (s1 - s2) + b1" by (simp add: x)
  have eq2: "s1 * (b2 - b1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + b1"
    by argo
  have eq3: "(b2 * s1 - b1 * s1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq4: "(b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)" 
    by argo
  have eq5: "s2 * x + b2 = s2 * (b2 - b1) / (s1 - s2) + b2" by (simp add: x)
  have eq6: "s2 * (b2 - b1) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + b2"
    by argo
  have eq7: "(b2 * s2 - b1 * s2) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq8: "(b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)"
    by argo
  have eq9: "y = s2 * x + b2"
    by (simp add: eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 y)
  have pm: "a2meets P m" 
    by (simp add: P mo eq9)
  thus ?thesis
    using a2parallel_def lo mo pl sdiff by auto   
qed

text\<open>\done Trying to prove axiom 2 directly seems near impossible. Let's start with 
something simpler: if l and m are parallel, and l is vertical, so is m (and similarly
for ordinary) \caleb\<close>

lemma A2_parallel_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x2 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2. m = A2Vertical s2 "

  by (metis A2_basics_1 a2ln.exhaust lm_parr lo)
    


text\<open> Let's do the other half of that: if l is ordinary, and m is parallel, then m is ordinary \<close>
lemma A2_parallel_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2 b2. m = A2Ordinary s2 b2 "
  by (metis A2_basics_1 a2ln.exhaust a2parallel_def lm_parr lo)
  

text\<open> And a third half: if l and m are parallel and ordinary, them their slopes are the same \<close>
lemma A2_parallel_3: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes mo: "m = A2Ordinary s2 b2 "
  assumes lm: "l a2|| m"

  shows "s1 = s2"
  using A2_basics_2 lm lo mo by blast 
 

text\<open>\done  Recall that axiom 2 states that there's a unique m 
through P, parallel to l.    
We'll phrase that just the way we did A1.a1b: \caleb \seiji\<close>
(* a2: "\<not> meets P l \<Longrightarrow> \<exists>!m. l || m \<and> meets P m" *)

lemma A2_a2b: 
  fixes P
  fixes l
  fixes m
  fixes k
  assumes pl : "\<not> a2meets P l"
  assumes pm : "a2meets P m"
  assumes pk : "a2meets P k"
  assumes lm_parr : "l a2|| m"
  assumes lk_parr : "l a2|| k"
  shows "m = k"
proof (cases m)
  case (A2Ordinary x11 x12)
  obtain xl yl where l_ord: "l = (A2Ordinary xl yl)"
    by (metis A2Ordinary A2_basics_1 a2meets.elims(3) lm_parr pl)
  obtain xk yk where k_ord: "k = (A2Ordinary xk yk)"
    using A2_parallel_2 l_ord lk_parr by blast
  have equality: "xl = xk \<and> x11 = xl"
    using A2Ordinary A2_basics_2 k_ord l_ord lk_parr lm_parr by force 
  have m_par_k: "m a2|| k"
    using A2Ordinary a2meets.elims(2) a2parallel_def equality k_ord by force
  then show ?thesis
    using a2parallel_def pk pm by blast
next
  case (A2Vertical x2)
  obtain xl where l_vert: "l = (A2Vertical xl)"
    by (metis A2Vertical A2_parallel_2 a2ln.distinct(1) a2meets.elims(3) lm_parr pl)
  obtain xk where k_vert: "k = (A2Vertical xk)"
    using A2_parallel_1 l_vert lk_parr by blast
  have equal: "xk = x2"
    by (metis A2Vertical a2meets.elims(2) a2meets.simps(2) k_vert pk pm)
  then show ?thesis
    using A2Vertical k_vert by auto
qed
lemma A2_a2: 
  fixes P
  fixes l
  assumes "\<not> a2meets P l"
  shows "\<exists>! m. a2meets P m \<and> m a2|| l"
  by (smt A2_a2a A2_a2b a2parallel_def)



lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
proof -
  obtain P where P: "P = (A2Point 0 0)" by simp
  obtain Q where Q: "Q = (A2Point 1 0)" by simp
  obtain R where R: "R = (A2Point 0 1)" by simp

  have "(\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
    by (metis A2_a1b P Q R a2meets.simps(2) a2pt.inject zero_neq_one)

  thus ?thesis
    by (metis (full_types) A2_a1 A2_a2)

qed
text\<open>\done \done\<close>

lemma A2_a3x:
  shows "\<not> (\<exists> m. a2meets (A2Point 0 0)  m \<and> a2meets (A2Point 0 1) m \<and> a2meets (A2Point 1 0) m)"

  by (metis A2_a1b a2meets.simps(1) a2pt.inject add.right_neutral mult_zero_left zero_neq_one)
  

lemma A2_a3y: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "\<not> (a2meets (A2Point 1 0) m)"
  using A2_a3x assms(1) assms(2) by blast

lemma A2_a3z1: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "m = (A2Vertical 0)"
  by (smt a2ln.inject(1) a2meets.elims(2) a2pt.inject assms(1) assms(2))

text\<open> At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined. \caleb \seiji 
\<close>

theorem A2_affine: "affine_plane UNIV UNIV a2meets"
  unfolding affine_plane_def
  apply (intro conjI)
  subgoal using A2_a1
    by simp
  subgoal
    by (smt A2_a2a A2_a2b a2parallel_def affine_plane_data.parallel.simps iso_tuple_UNIV_I) 
  apply (simp add: affine_plane_data.collinear.simps)
  using A2_a3 by auto


text\<open>\done \done  Examples of some easy theorems about affine planes, not mentioned in Hartshorne. \jackson \<close>      



(* Some HW Problems to give you practice with Isabelle:
Try to state and prove these:
1. Every line contains at least two points (this is stated for you below, but
with "sorry" as a "proof". 
2. Every line contains at least three points [false!]
*)

text\<open>To prove that every line contains at least two points, firstly we should think about where the
contradiction is when the line contains only one point. Usually, contradiction happens when something
violates a unique existence. For example, in A2, if an assumption leads to the conclusion that there
are more lines that could parallel to a specific line passing through the same point, then the assumption
is proved to be false. Here are the ideas for our proof.

i. If l only contains one point Q and point P != point Q, then every line passing through P is parallel
to l.
ii. To prove the contradiction to A2, we have to prove there are at least two lines passing through P. 
NB: need lemma contained-lines: for every point, there are at least two lines that pass through that point.
iii.Lemma contained-lines can be proved with the three non-collinear points P Q R in A3. Two cases:
1. The point is P or Q or R. 2. The point T is different from those 3 points. Then PT, QT, RT cannot
be the same line, which proves that at least two lines pass through T.

(I'm still Struggling with the grammar in Isabelle. I’ll try to finish these two lemmas soon and
 I’m also looking for help ;)
\siqi\<close>
lemma (in affine_plane) contained_lines: "\<forall> S \<in> Points. \<exists>l m. l \<in> Lines \<and> m \<in> Lines \<and> l\<noteq>m \<and> meets S l \<and> meets S m"
sorry 
(*
proof -
  obtain P Q R where PQR: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
    using a3 by auto
  fix S
  show ?thesis
  proof (cases "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R")
    case True
    then obtain SP where SP: " meets S SP \<and> meets P SP"
      using a1 by blast
    obtain SR where SR: "meets S SR \<and> meets R SR" 
      using True a1 by blast
    obtain SQ where SQ: "meets S SQ \<and> meets Q SQ"
      using True a1 by blast
    have nosameline: "\<nexists>l. l=SP \<and> l=SQ \<and> l=SR" try
      using PQR SP SQ SR affine_plane_data.collinear_def by force
    have differtwolines: "SP \<noteq> SQ \<or> SP \<noteq> SR \<or> SQ \<noteq> SR"
      using nosameline by auto
    then show "\<exists>l,m \<in> {SP, SQ, SR}. l\<noteq>m \<and> meets S l \<and> meets S m"
    show ?thesis
      sorry
  next
    case False
    show ?thesis
  proof (cases "S = P")
    case True
    then obtain SQ1 where SQ1: "meets S SQ1 \<and> meets Q SQ1"
      by (metis PQR affine_plane.a1 affine_plane_axioms)
    obtain SR1 where SR1: "meets S SR1 \<and> meets R SR1"
      by (metis PQR a1)
    have nosameline1: "SQ1 \<noteq> SR1" 
      using PQR SQ1 SR1 True affine_plane_data.collinear_def by force
    have "SQ1 \<noteq> SR1 \<and> meets S SQ1 \<and> meets S SR1"try
      by (simp add: SQ1 SR1 nosameline1)
    show ?thesis
      sorry
    next 
      case False
      show ?thesis
      proof (cases "S = Q")
        case True
        then obtain SP2 where SP2: "meets S SP2 \<and> meets P SP2" 
          using False affine_plane.a1 affine_plane_axioms by fastforce
        obtain SR2 where SR2: "meets S SR2 \<and> meets R SR2"
          by (metis PQR a1)
        have nosameline2: "SP2 \<noteq> SR2"
          using PQR SP2 SR2 True affine_plane_data.collinear_def by force
        have "SP2 \<noteq> SR2 \<and> meets S SP2 \<and> meets S SR2"
          using SP2 SR2 nosameline2 by blast
        show ?thesis
          sorry
        case False
        then obtain SP3 where SP3: "meets S SP3 \<and> meets P SP3"
          using True by blast
        obtain SQ3 where SQ3: "meets S SQ3 \<and> meets Q SQ3"
          using False True by blast
        have nosameline3: "SP3 \<noteq> SQ3"
          using False True by auto
        have "SP3 \<noteq> SQ3 \<and> meets S SP3 \<and> meets S SQ3"
          using False True by auto
*)


  text \<open>
 We now try to prove that every affine plane contains at least four points. Sledgehammer 
(a generally-useful approach) doesn't get anywhere with this one. 

Here's Hartshorne's proof, though, so we can use the pieces to construct an Isabelle proof.

i. by A3 there are three distinct non-collinear points; call them P,Q,R. 
ii. By A1, there's a line, which I'll call QR, through Q and R. 
iii. By A2, there's a line l through P, parallel to QR.
iv. Similarly, there's a line PQ containing P and Q. 
v. There's a line m through R, parallel to the line PQ.

CASES: l is parallel to m, or it is not.  

vi. l is not parallel to m, for if it were, then PQ || m || l || QR, hence PQ || QR (by 
the lemmas about parallelism) and since both contain Q,  they are identical, but then P,Q,R are collinear,
which is a contradiction. 

vii. So l and m are nonparallel, and they share some point S. 

viii. S lies on m, which is parallel to PQ but not equal to it,
hence disjoint from it (see definition of parallel), so S is not on PQ.

ix.  Hence S != P, S != Q. 

x. Similar (arguing about l), we get  S != R. 

xi. Hence the four points P,Q,R,S are all distinct, and we are done. 
\caleb \seiji\<close>
proposition (in affine_plane) four_points_necessary: "\<exists>P Q R S. 
      P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> S \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S"
    proof -
      obtain P Q R where PQR: "P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"
        using a3 by blast
      obtain PQ where PQ: "PQ \<in> Lines \<and> meets P PQ \<and> meets Q PQ" 
        using a1 PQR by blast
      obtain l where l: "l \<in> Lines \<and> meets R l \<and> l || PQ"
        by (metis PQ PQR affine_plane.a2 affine_plane.symmetric_parallel affine_plane_axioms collinear.simps)
      obtain QR where QR: "QR \<in> Lines \<and> meets Q QR \<and> meets R QR"
        using a1 PQR by blast
      obtain m where m: "m \<in> Lines \<and> meets P m \<and> m || QR"
        by (metis QR PQR affine_plane.a2 affine_plane.symmetric_parallel affine_plane_axioms collinear.simps)
      obtain S where S: "S \<in> Points \<and> meets S l \<and> meets S m"
        using PQ QR affine_plane.a2 affine_plane_axioms l m 
        by (metis PQR parallel.simps)
      have "S \<noteq> P \<and> S \<noteq> Q \<and> S \<noteq> R"
        by (metis PQ PQR QR S collinear.simps parallel.simps l m)
      thus ?thesis
        using PQR
        using S by blast
    qed

    text\<open>\done \done\<close>
    section \<open>Free projective plane\<close>
    text\<open>\spike 
We've now proved the first assertion in the Example after Prop 1.2; we must also show there
IS an affine plane with four points. We'll do this two ways: by explicit construction, and
by using the wonderful ``nitpick'' prover.

We start by defining two datatypes, each of which is just an enumerated type; there
are four points and six suggestively-named lines:
\done\<close>

  



datatype pts = Ppt | Qpt | Rpt | Spt
datatype lns = PQln | PRln | PSln | QRln | QSln | RSln
text\<open>\spike 
Note: the above datatypes are meant to indicate that ``pts'' consists of four constructors,
one for each of $P,Q,R$ and $S$, and that the line we'd call $PQ$ in math is here 
constructed with
$PQln$, and we'll define the point-to-line meeting function (i.e., "the point is on the line" so that 
$P$ and $Q$ are on $PQln$, but $R$ and $S$ are not, etc. 

For the "meets" definition, the syntax looks OCaml-like.

We start by saying which points \emph{are} on the various lines, and then follow with those that
are not.
\done\<close>
  fun plmeets :: "pts \<Rightarrow> lns \<Rightarrow> bool" where
    "plmeets Ppt PQln = True" |
    "plmeets Qpt PQln = True" |
    "plmeets Ppt PRln = True" |
    "plmeets Rpt PRln = True" |
    "plmeets Ppt PSln = True" |
    "plmeets Spt PSln = True" |
    "plmeets Qpt QRln = True" |
    "plmeets Rpt QRln = True" |
    "plmeets Qpt QSln = True" |
    "plmeets Spt QSln = True" |
    "plmeets Rpt RSln = True" |
    "plmeets Spt RSln = True" |

    "plmeets Rpt PQln = False" |
    "plmeets Spt PQln = False" |
    "plmeets Qpt PRln = False" |
    "plmeets Spt PRln = False" |
    "plmeets Qpt PSln = False" |
    "plmeets Rpt PSln = False" |
    "plmeets Ppt QRln = False" |
    "plmeets Spt QRln = False" |
    "plmeets Ppt QSln = False" |
    "plmeets Rpt QSln = False" |
    "plmeets Ppt RSln = False" |
    "plmeets Qpt RSln = False"

text\<open>\spike 
  Now we'll assert that "plmeets" has all the properties needed to be an affine plane.
\done\<close>
  lemma four_points_a1: "P \<noteq> Q \<Longrightarrow> \<exists>! l . plmeets P l \<and> plmeets Q l"
    by (smt plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(13) plmeets.simps(14) plmeets.simps(17) plmeets.simps(18) plmeets.simps(19) plmeets.simps(2) plmeets.simps(20) plmeets.simps(22) plmeets.simps(23) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

  lemma four_points_a2a (*existence*): "\<not> plmeets (P :: pts) (l :: lns) \<Longrightarrow> \<exists>m. ((l = m)\<or> \<not> (\<exists> T. plmeets T l  \<and> plmeets T m)) \<and> plmeets P m"
    by (smt lns.simps(27) lns.simps(5) lns.simps(7) plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(15) plmeets.simps(16) plmeets.simps(17) plmeets.simps(18) plmeets.simps(2) plmeets.simps(22) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

text\<open>\spike 
Exercise: change the first "$\lor$" in the lemma above to "$\land$"; that makes the lemma no longer true.
Attempt to prove it with "try" and then make sense of what the output is saying. 
\done\<close>

  lemma four_points_a2b(*uniqueness*): 
    "\<lbrakk>\<not> plmeets (P :: pts) (l :: lns); plmeets P m;  \<not> (\<exists> T. plmeets T l  \<and> plmeets T m); 
      plmeets P n;  \<not> (\<exists> U. plmeets U l  \<and> plmeets U n)\<rbrakk> 
     \<Longrightarrow> m = n"
    by (smt plmeets.elims(3) plmeets.simps(1) plmeets.simps(11) plmeets.simps(2) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.simps(11) pts.simps(5) pts.simps(9))


  lemma four_points_a2: 
    "\<not> plmeets (P :: pts) (l :: lns) \<Longrightarrow> \<exists>!m. ((l = m)\<or> \<not> (\<exists> T. plmeets T l  \<and> plmeets T m)) \<and> plmeets P m" 
    using four_points_a2a four_points_a2b
    by auto

  lemma four_points_a3:  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<not> (\<exists> m. plmeets P m \<and> plmeets Q m \<and> plmeets R m))"
    using four_points_a1 plmeets.simps(1) plmeets.simps(13) plmeets.simps(2) by blast

text\<open>\spike 
We now prove that the four-point plane is in fact an affine plane (which should surprise no 
one who's gotten this far). There are two proofs of this given below. The second one was one 
discovered by sledgehammer, and is an "apply-style" proof, i.e., the kind of proof that was common 
in Isabelle before Isar. The first is an Isar-style proof that's based on the apply-style proof (i.e., 
we took the second proof in class and collectively converted it, line by line, to the Isar 
proof. The Isar proof is quite a lot longer, partly because we didn't know how to say "let's work 
on just goal 1" and instead had to paste in all of goal 1 (or 2, or 3, or whatever). 
\done\<close>



proposition four_points_sufficient: "affine_plane UNIV UNIV plmeets"
proof -
  show ?thesis unfolding affine_plane_def 
  proof (rule conjI)
    show " \<forall>P Q. P \<noteq> Q \<longrightarrow> P \<in> UNIV \<longrightarrow> Q \<in> UNIV \<longrightarrow>
          (\<exists>!l. l \<in> UNIV \<and> plmeets P l \<and> plmeets Q l)"
      using four_points_a1 by simp
    show ax1: "(\<forall>P l. \<not> plmeets P l \<longrightarrow> P \<in> UNIV \<longrightarrow> l \<in> UNIV \<longrightarrow>
           (\<exists>!m. m \<in> UNIV \<and> affine_plane_data.parallel  UNIV UNIV plmeets l m \<and> plmeets P m)) \<and>
    (\<exists>P Q R. P \<in> UNIV \<and>Q \<in> UNIV \<and> R \<in> UNIV \<and> P \<noteq> Q \<and>  P \<noteq> R \<and> Q \<noteq> R \<and>
        \<not> affine_plane_data.collinear UNIV UNIV plmeets P Q R)"
    proof (rule conjI)
      show ax2: " \<forall>P l. \<not> plmeets P l \<longrightarrow> P \<in> UNIV \<longrightarrow> l \<in> UNIV \<longrightarrow>
          (\<exists>!m. m \<in> UNIV \<and> affine_plane_data.parallel UNIV UNIV plmeets l m \<and>plmeets P m)" 
        using four_points_a2 iso_tuple_UNIV_I
        by (simp add: affine_plane_data.parallel.simps)
      show ax3: "\<exists>P Q R. P \<in> UNIV \<and> Q \<in> UNIV \<and> R \<in> UNIV \<and> P \<noteq> Q \<and> P \<noteq> R \<and>  Q \<noteq> R \<and>
                \<not> affine_plane_data.collinear UNIV UNIV plmeets P Q R" 
        using four_points_a3 by (simp add:affine_plane_data.collinear.simps)
    qed
  qed
qed

proposition four_points_sufficient2: "affine_plane UNIV UNIV plmeets"
    unfolding affine_plane_def
    apply (intro conjI)
    subgoal using four_points_a1 by simp
    subgoal using four_points_a2 iso_tuple_UNIV_I
      by (simp add: affine_plane_data.parallel.simps)
    apply (simp add: affine_plane_data.collinear.simps)
    using four_points_a3 apply (blast)
    done

text\<open>\spike 
There's another way to show the existence of a 4-point affine plane: you claim that they
must have at least $5$ points, and let ``nitpick'' show that you're wrong. I'm going to use some
fancy mumbo-jumbo to write this so I can avoid writing out all the pairwise non-equalities; 
this fanciness is due to Manuel Eberl.

\begin{lstlisting}[language=Isabelle]{}
begin
  fix meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
  assume "affine_plane meets"

  have "\<exists>A::'point set. finite A \<and> card A = 5"
    by nitpick
end
\end{lstlisting}

To actually see what that produces, you'll need to type the code above into Isabelle. 
The results are pretty nifty, though,  hunh? 
It's a pain to try to read the output, but the gist is pretty clear: 4 points,
6 lines, each consisting of two distinct points.
\done\<close>

text  \<open> 
\begin{hartshorne}
\defn{Pencil} A pencil of lines is either a) the set of all lines passing through some point 
$P$ , or b) the set of all lines parallel to some line $l.$ In the second case we speak of 
a ``pencil of parallel lines.''

\defn{One-to-one correspondence} A one-to-one correspondence between two sets $X$ and $Y$ is a 
mapping $T : X \to Y$ (i.e., a rule $T,$ which associates to each element $x$ of the set
$X$ an element $T(x)=y 
\in Y$ such that $x_1\ne x_2 \implies T(x_1) \ne T(x_2),$ and
$\forall y \in Y, \exists x \in X$ such that $T(x)=y.$
\end{hartshorne}
\<close>
fun (in affine_plane_data) point_pencil :: "'p  \<Rightarrow> 'l set"
    where "point_pencil P = (if P \<in> Points then {l . meets P l} else {})"

fun (in affine_plane_data) line_pencil :: "'l  \<Rightarrow> 'l set"
    where "line_pencil l = (if l \<in> Lines then {m .  l||m} else {})"

definition (in affine_plane_data) points_on_line :: "'line \<Rightarrow> 'point set"
  where "points_on_line l = {P. meets P l}"

lemma (in affine_plane) lines_same_card:
  fixes l :: 'line
  fixes m :: 'line
  shows "card(points_on_line l) = card(points_on_line m)"
  sorry

  (* given two points on a line in an affine plane, there must be a third point *)
lemma (in affine_plane) third_pt_off_line: 
  fixes l ::'line
  assumes "card(points_on_line l) = 2"
  shows "\<exists> R. \<not> meets R l"
proof -
  obtain P Q where PQ: "P \<noteq> Q \<and> P \<in> (points_on_line l) \<and> Q \<in> (points_on_line l)"
    using affine_plane_data.points_on_line_def contained_points by fastforce
  obtain R where R: "\<not> meets R l"
    using a3 collinear_def by blast
  show ?thesis
    using R by blast
qed

text  \<open> 
\spike
  I've skipped the notion of 1-1 correspondence, because Isabelle already has a notion 
  of bijections: there's a function "bij" that consumes a function and produces a boolean.
\done
\<close>





text  \<open> 
\spike
Completion of an affine plane to a projective plane 

Small problem: we need a data type for the points of the projective plane, which consists of
     all points of the affine plane together with all ideal points (i.e., line pencils), and we 
     need another for the lines of the PP, which consists of all lines of the affine plane (extended 
     by their associated ideal point) and the line at infinity consisting of all ideal points. We'll
     return to this, but first we need axioms for a projective plane.

The main problem is that we really, really need quotient types; with luck, Haoze and Daniel will 
soon have worked these out for us so that we can proceed. 
\done
\<close>

section \<open>The projective plane\<close>
text  \<open> 
\begin{hartshorne}
\section*{Ideal points and the projective plane}

We will now complete the affine plane by adding certain ``points at infinity'' and thus arrive at 
the notion of the projective plane.

Let $A$ be an affine plane. For each line $l \in A,$ we will denote by $[l]$ the pencil of lines 
parallel to $l,$ and we will call $[l]$ an ``ideal point,'' or ``point at infinity,'' in the 
direction of $l.$ We write $P^{*} = [l]$.

We define the completion $S$ of $A$ as follows. The points of $S$ are the points of $A,$ plus all 
the ideal points of $A.$ A line in $S$ is either

\begin{enumerate}
\item An ordinary line $l$ of $A,$ plus the ideal point $P^{*} = [l]$ of $l$, or 
\item the ``line at infinity,'' consisting of all the ideal points of $A.$
\end{enumerate}

We will see shortly that $S$ is a projective plane, in the sense of the following definition.

\defn[Projective Plane] A ``projective plane'' $S$ is a set, whose elements are called points, 
and a set of subsets, called lines, satisfying the following four axioms.
\begin{enumerate}
\item[P1] Two distinct points $P, Q$ of $S$ lie on one and only one line. 
\item[P2] Any two lines meet in at least one point.
\item[P3] There exist three non-collinear points.
\item[P4] Every line contains at least three points.
\end{enumerate}

\prop[1.3] The completion $S$ of an affine plane $A,$ as described above, is a projective plane.

\proof. We must verify the four axioms P1–P4 of the definition. 
       
P1. Let $P,Q  \in S$.
\begin{enumerate}
\item If $P,Q$  are ordinary points of $A,$ then $P$ and $Q$ lie on only one line of $A.$ They do not 
lie on the line at infinity of $S,$ hence they lie on only one line of $S.$

\item If $P$ is an ordinary point, and $Q = [l]$ is an ideal point, we can find by A2 a line $m$ 
such that $P \in m$ and $m \parallel l$,i.e. $m \in [l]$,so that $Q$  lies on the extension of $m$ 
to $S.$ This is clearly the only line of $S$ containing $P$ and $Q.$

\item If $P, Q$ are both ideal points, then they both lie on the line of $S$ containing them.
\end{enumerate}

P2. Let $l, m$ be lines. 
\begin{enumerate}
\item If they are both ordinary lines, and $l \nparallel m,$ then they meet
in a point of $A.$ If $l \parallel m,$ then the ideal point $P^{*} =[l]=[m]$ lies on both $l$ and
$ m$ in $S.$
\item If $l$ is an ordinary line, and $m$ is the line at infinity, then $P^{*} = [l]$ lies on 
both $l$ and $m.$
\end{enumerate}

P3. Follows immediately from A3. One must check only that if $P,Q,R$ are non-collinear in $A,$ then
 they are also non-collinear in $S.$ Indeed, the only new line is the line at infinity, 
which contains none of them.

P4. Indeed, by Problem 1, it follows that each line of $A$ contains at least two points. 
Hence, in $S$ it has also its point at infinity, so has at least three points. \endproof

Examples. 

\begin{enumerate}
\item By completing the real affine plane of Euclidean geometry, we obtain the real projective plane.
\item By completing the affine plane of $4$ points, we obtain a projective plane with $7$ points.
\item Another example of a projective plane can be constructed as follows: let $\Bbb R^3$ be 
ordinary Euclidean 3-space, and let $O$ be a point of $\Bbb R^3.$ Let $L$ be the set of lines 
through $O.$

We define a point of $L$ to be a line through $O$ in $\Bbb R^3.$ We define a line of $L$ to be 
the collection of lines through $O$ which all lie in some plane through $O.$
Then $L$ satisfies the axioms P1–P4 (left to the reader), and so it is a projective plane.
\end{enumerate}
\end{hartshorne}
\spike
We'll go ahead and formalize the notion of projective plane as we did earlier; we won't prove 
proposition 1.3 (in Isabelle) until we have a good tool for quotient types, but we'll proceed 
with the work on the 7-point plane, etc.
\done
\<close>
  locale projective_plane_data =
    fixes Points :: "'point set" and Lines :: "'line set" and meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

  begin
    fun collinear :: "'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> meets A l \<and> meets B l \<and> meets C l) else False)"

    fun concurrent :: "'line  \<Rightarrow> 'line \<Rightarrow> 'line \<Rightarrow> bool"
      where "concurrent l m n \<longleftrightarrow> (if l \<in> Lines \<and> m \<in> Lines \<and> n \<in> Lines then 
  (\<exists> P. meets P l \<and> meets P m \<and> meets P n) else False)"
 
    definition injective :: "('a  \<Rightarrow> 'b)  \<Rightarrow> bool"
      where "injective f  \<longleftrightarrow> ( \<forall> P Q.  (f(P) = f(Q)) \<longleftrightarrow> (P = Q))" 

    definition points_of :: "'line \<Rightarrow> 'point set" where "points_of k = (if k \<in> Lines then {P \<in> Points . meets P k} else undefined)"
    definition lines_of :: "'point \<Rightarrow> 'line set" where "lines_of P = (if P \<in> Points then {k \<in> Lines . meets P k} else undefined)"
    
    definition joinline :: "'point \<Rightarrow> 'point \<Rightarrow> 'line" where "joinline P Q = (if (P \<noteq> Q \<and> P \<in> Points \<and> Q \<in> Points)
                                                                              then (THE l . l \<in> Lines \<and> meets P l \<and> meets Q l) 
                                                                              else undefined)"
  end                   
                        

  locale projective_plane =
    projective_plane_data +
  assumes
    p1: "\<lbrakk>P\<in>Points; Q \<in> Points; P \<noteq> Q\<rbrakk> \<Longrightarrow> \<exists>!l. l \<in> Lines \<and> meets P l \<and> meets Q l" and
    p2: "\<lbrakk>l\<in> Lines; m \<in> Lines; l \<noteq> m\<rbrakk> \<Longrightarrow> \<exists>!P. P \<in> Points \<and>  meets P l \<and> meets P m" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R" and
    p4: "\<forall> l \<in> Lines. \<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> meets P l \<and> meets Q l \<and> meets R l"

begin

(* right here is where many small theorems about projective planes should go, theorems like "any
two lines in a projective plane have the same cardinality", etc. -- Spike *)

text  \<open> 
\spike
Here we have a few small theorems about projective planes, some from the exercises in Hartshorne,
others that just arose during class. 
 \done
\<close>

lemma pointOffLines:
  fixes l and m
  assumes "l \<noteq> m"
  assumes lines: "l \<in> Lines \<and> m \<in> Lines"
  shows "\<exists>T. T \<in> Points \<and> (\<not> meets T l) \<and> (\<not> meets T m)"
proof -
  obtain I where I: "I \<in> Points \<and> meets I l \<and> meets I m" 
    using p2 assms by blast
  obtain P where P: "P \<in> Points \<and> meets P l \<and> P \<noteq> I" 
    using assms p4 I by metis
  obtain Q where Q: "Q \<in> Points \<and> meets Q m \<and> Q \<noteq> I"
    using assms p4 I by metis
   obtain PQ where PQ: "PQ \<in> Lines \<and> meets P PQ \<and> meets Q PQ"
    using P Q p1
    using lines by fastforce
  obtain R where R: "R \<in> Points \<and> meets R PQ \<and> P \<noteq> R \<and> Q \<noteq> R"
    using p4 
    by (metis PQ)
  have not_on_l: "\<not> meets R l"
    by (metis I P PQ Q R assms(1) lines p1)   
  have not_on_m: "\<not> meets R m"
    by (metis I P PQ Q R assms(1) lines p1)   
  thus ?thesis
    using not_on_l
    using R by blast 
qed

text \<open>\homer\<close>

(* joinline returns a unique line when conditions are met *)
lemma joinline_exists:
  fixes P and Q and x
  assumes "P \<noteq> Q" and "x = (joinline P Q)" and "P \<in> Points" and "Q \<in> Points"
  shows "x \<in> Lines \<and> meets P x \<and> meets Q x"
proof -
  show ?thesis using assms p1 [of P Q] joinline_def [of P Q] theI_unique by smt
qed
lemma joinline_unique:
  fixes P and Q and x
  assumes "P \<noteq> Q" and "x = (joinline P Q)" and "P \<in> Points" and "Q \<in> Points"
  shows "\<nexists> y . y \<in> Lines \<and> meets P y \<and> meets Q y \<and> x \<noteq> y"
proof -
  show ?thesis using assms p1 [of P Q] joinline_def [of P Q] theI_unique by smt
qed
 
(* for a line and a point not on the line the number of lines that meet
   the point is equal to the number of points on the line *)
lemma line_point_off_bij:
  fixes l and P
  assumes "\<not> meets P l" and "P \<in> Points" and "l \<in> Lines"
  shows "bij_betw (joinline P) (points_of l) (lines_of P)"
proof -
  have "inj_on (joinline P) (points_of l)"
    using assms inj_onI joinline_exists joinline_unique mem_Collect_eq points_of_def projective_plane_axioms 
    by smt
  have "\<forall> m \<in> (lines_of P) . \<exists> Q \<in> (points_of l) . (joinline P Q) = m"
    using assms joinline_unique lines_of_def mem_Collect_eq p2 points_of_def
    by (metis (no_types, lifting))
  then have "(joinline P) ` (points_of l) = (lines_of P)"
    unfolding image_def points_of_def lines_of_def
    using Collect_cong assms mem_Collect_eq joinline_exists projective_plane_axioms by smt
  thus ?thesis
    using \<open>inj_on (joinline P) (points_of l)\<close> bij_betw_def by blast
qed

(* for a line and a point on that line there exists another line that doesn't meet the point *)
lemma second_line:
  fixes l and P
  assumes "meets P l" and "P \<in> Points" and "l \<in> Lines"
  shows "\<exists> k . k \<in> Lines \<and> \<not> meets P k"
proof -
  obtain m where "m \<noteq> l \<and> m \<in> Lines"
    by (metis (full_types) collinear.elims(3) p1 p3)
  show ?thesis
proof (cases "meets P m")
  case False
  then show ?thesis
    using \<open>m \<noteq> l \<and> m \<in> Lines\<close> by blast
next
  case True
  obtain X where "meets X l \<and> X \<noteq> P \<and> X \<in> Points"
    using p4 assms(3) by blast
  obtain Y where "meets Y m \<and> Y \<noteq> P \<and> Y \<in> Points"
    using p4 \<open>m \<noteq> l \<and> m \<in> Lines\<close> by blast
  then obtain k where "meets X k \<and> meets Y k \<and> k \<in> Lines"
    using \<open>meets X l \<and> X \<noteq> P \<and> X \<in> Points\<close> joinline_exists assms(3) by metis
  thus ?thesis
    by (metis \<open>m \<noteq> l \<and> m \<in> Lines\<close> \<open>meets X l \<and> X \<noteq> P \<and> X \<in> Points\<close> \<open>meets Y m \<and> Y \<noteq> P \<and> Y \<in> Points\<close> assms(2) assms(3) joinline_unique)
qed
qed

(* for every line and a point off that line the number of points on the line is equal to 
   the number of lines that meet the point *)
lemma line_point_off_same_card:
  fixes l and P
  assumes "\<not> meets P l" and "P \<in> Points" and "l \<in> Lines"
  assumes "card (lines_of P) = n"
  shows "card (points_of l) = n"
  using assms bij_betw_same_card line_point_off_bij by blast

(* for every line and point the number of points on the line is equal to 
   the number of lines that meet the point *)
lemma line_point_same_card:
  fixes l and P
  assumes "card (lines_of P) = n" and "P \<in> Points" and "l \<in> Lines"
  shows "card (points_of l) = n"
proof (cases "meets P l")
  case True
  obtain k where "k \<in> Lines \<and> \<not> meets P k" using second_line
    using assms(2) assms(3) by auto
  then obtain Q where "Q \<in> Points \<and> \<not> meets Q l \<and> \<not> meets Q k"
    using pointOffLines True assms(3) by force
  then have "bij_betw (joinline Q) (points_of l) (lines_of Q)"
    using line_point_off_bij assms(3) by auto
  have "bij_betw (joinline Q) (points_of k) (lines_of Q)"
    using \<open>Q \<in> Points \<and> \<not> meets Q l \<and> \<not> meets Q k\<close> line_point_off_bij \<open>k \<in> Lines \<and> \<not> meets P k\<close> by auto
  have "bij_betw (joinline P) (points_of k) (lines_of P)"
    using \<open>k \<in> Lines \<and> \<not> meets P k\<close> line_point_off_bij assms(2) by simp
  thus ?thesis
    by (metis \<open>bij_betw (joinline Q) (points_of k) (lines_of Q)\<close> \<open>bij_betw (joinline Q) (points_of l) (lines_of Q)\<close> assms(1) bij_betw_same_card)
next
  case False
  then have "bij_betw (joinline P) (points_of l) (lines_of P)" 
    using line_point_off_bij assms(2) assms(3) by simp
  then show ?thesis
    using assms bij_betw_same_card by auto
qed

(* all lines have n points *)
lemma lines_same_card: "\<exists> n . \<forall> l \<in> Lines . card(points_of l) = n"
  using line_point_same_card p3 by blast

(* all points meet n lines *)
lemma points_same_card: "\<exists> n . \<forall> P \<in> Points . card(lines_of k) = n"
  using line_point_same_card by auto

(* removing an element from a set reduces cardinality by 1 *)
lemma minus_card:
  fixes C and q
  assumes "q \<in> C" and "card C = n"
  shows "card (C - {q}) = n - 1"
  by (simp add: assms card_Diff_subset)

(* if a line has n points, the plane has n*(n-1) + 1 points *)
lemma line_points_to_plane_points:
  fixes l
  assumes "l \<in> Lines" 
  assumes "n = card(points_of l)" and "finite (points_of l)"
  shows "card Points = n * (n-1) + 1"
proof -
  obtain Q where 0: "Q \<in> Points \<and> meets Q l"
    using p4 assms(1) by auto
  obtain Q_lines where 1: "Q_lines = lines_of Q" by simp
  then have 2: "card(Q_lines) = n"
    using assms(2) line_point_same_card 0 assms(1) by auto
  have 3: "finite Q_lines"
    using 1 assms(3) 0 assms(1) bij_betw_finite line_point_off_bij pointOffLines second_line 
    by metis
  have 4: "\<forall> x \<in> Q_lines . x \<in> Lines"
    using 1 lines_of_def 0 by simp
  have 5: "inj_on points_of Q_lines"
  proof (rule ccontr)
    assume 6: "\<not> inj_on points_of Q_lines"
    then obtain x y where 7: "x \<in> Lines \<and> y \<in> Lines \<and> x \<noteq> y \<and> (points_of x) = (points_of y)"
      by (meson 4 inj_on_def)
    then obtain R S where 8: "R \<in> Points \<and> S \<in> Points \<and> meets R x \<and> meets S x \<and> R \<noteq> S"
      using p2 p4 by auto
    then have 9: "R \<in> points_of x \<and> S \<in> points_of x"
      using points_of_def 7 by simp
    then have 10: "R \<in> points_of y \<and> S \<in> points_of y"
      using 7 by simp
    then have 11: "meets R y \<and> meets S y"
      using points_of_def 7 by simp
    then show False using p1 7 8 by auto
  qed
  obtain Q_lines_points where 13: "Q_lines_points = points_of ` Q_lines" by simp
  then have 14: "\<forall> x \<in> Q_lines_points . \<forall> y \<in> Q_lines_points . x \<noteq> y \<longrightarrow> (\<nexists> P . P \<in> Points \<and> P \<in> x \<and> P \<in> y \<and> P \<noteq> Q)"
    using 1 imageE lines_of_def mem_Collect_eq p1 points_of_def 0 by smt
  have 15: "card Q_lines_points = n"
    using card_image 5 13 2 by blast
  have 16: "finite Q_lines_points"
    using 3 by (simp add: 13)
  have 17: "\<forall> m \<in> Lines . finite (points_of m)"
    using assms(1) assms(3) bij_betw_finite line_point_off_bij pointOffLines by metis
  then have 18: "\<forall> m \<in> Q_lines . finite (points_of m)"
    by (simp add: 1 0 lines_of_def)
  then have 19: "finite (\<Union> Q_lines_points)"
    using 3 finite_UN 13 by simp
  have 20: "\<forall> x \<in> \<Union> Q_lines_points . x \<in> Points"
    using 13 points_of_def 4 by simp
  have 21: "\<forall> k \<in> Q_lines_points . Q \<in> k"
    using 1 13 lines_of_def points_of_def 0 assms(1) by simp
  have 23: "\<forall> k \<in> Q_lines_points . card k = n"
    using 13 assms lines_same_card 4 by auto
  obtain Q_lines_points_no_Q where 24: "Q_lines_points_no_Q = (\<lambda>x. x - {Q}) ` Q_lines_points"
    by simp
  have 25: "inj_on (\<lambda>x. x - {Q}) Q_lines_points"
  proof (rule ccontr)
    assume 26: "\<not> inj_on (\<lambda>x. x - {Q}) Q_lines_points"
    then obtain A B where 27: "A \<in> Q_lines_points \<and> B \<in> Q_lines_points \<and> (\<lambda>x. x - {Q}) A = (\<lambda>x. x - {Q}) B \<and> A \<noteq> B"
      using inj_on_def
      by (metis (mono_tags, lifting))
    then obtain R where 28: "R \<in> Points \<and> R \<in> A \<and> R \<in> B \<and> R \<noteq> Q"
      using p2 p4 21 by auto
    then obtain a b where 29: "a \<in> Lines \<and> b \<in> Lines \<and> meets R a \<and> meets Q a \<and> meets R b \<and> meets Q b \<and> a \<noteq> b"
      using 27 21 by auto
    then show False using p1 0 28 by auto
  qed
  then have 30: "card Q_lines_points_no_Q = n"
    using 15 card_image 24 by blast
  have 31: "finite Q_lines_points_no_Q"
    using 16 24 by simp
  then have 32: "finite (\<Union> Q_lines_points_no_Q)"
    using 19 24 by simp
  have 33: "\<forall> r \<in> Q_lines_points_no_Q . \<forall> s \<in> Q_lines_points_no_Q . r \<noteq> s \<longrightarrow> r \<inter> s = {}"
    using 14 24 20 by auto
  have 34: "\<forall> k \<in> Q_lines_points_no_Q . card k = n - 1"
    using 21 23 24 minus_card by force
  then have 35: "(n - 1) * card(Q_lines_points_no_Q) = card(\<Union> Q_lines_points_no_Q)"
    by (simp add: 33 31 32 card_partition)
  then have 36: "card(\<Union> Q_lines_points_no_Q) = (n - 1) * n" 
    using 30 by simp
  have 37: "\<nexists> R . R \<in> Points \<and> R \<notin> \<Union> Q_lines_points"
  proof (rule ccontr)
    assume 38: "\<not> (\<nexists> R . R \<in> Points \<and> R \<notin> \<Union> Q_lines_points)"
    then obtain R where 39: "R \<in> Points \<and> R \<notin> \<Union> Q_lines_points" by auto
    then obtain k where 40: "k \<in> Lines \<and> meets R k \<and> meets Q k"
      using p1 0 assms(1) by blast
    then have 41: "k \<in> Q_lines" using 1 lines_of_def 0 by simp
    have 42: "R \<in> (points_of k)" using 40 points_of_def
      by (simp add: 39)
    then have 43: "R \<in> \<Union> Q_lines_points" using 41 13 by auto
    then show False using 39 43 by blast
  qed
  have 45: "\<Union> Q_lines_points \<subseteq> Points" using 20 by auto
  have 46: "Points \<subseteq> \<Union> Q_lines_points"
    using 37 by blast
  have 47: "Points = \<Union> Q_lines_points"
    by (simp add: 46 45 set_eq_subset)
  have 48: "\<Union> Q_lines_points_no_Q = (\<Union> Q_lines_points) - {Q}" using 13 24 by simp
  then have 50: "card (\<Union> Q_lines_points_no_Q) = card (Points - {Q})" using 47 by simp
  have 51: "Q \<in> Points \<and> {Q} \<subseteq> Points"
    by (simp add: 0)
  then have 53: "card (Points - {Q}) = card Points - card {Q}" by (simp add: card_Diff_subset)
  then have 54: "card Points = card (\<Union> Q_lines_points_no_Q) + card {Q}"
    by (metis 47 50 19 51 card_mono le_add_diff_inverse2)  
  show ?thesis using 54 36 by simp
qed

text \<open>\done\<close>

end

  (* Pending: The "Ideal" constructor probably needs to take a pencil of lines, or a quotient type *)
  datatype ('point, 'line) projPoint = Ordinary 'point | Ideal 'line
  datatype ('point, 'line) projLine = OrdinaryL 'line | Infty 

  fun projectivize :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b) projPoint \<Rightarrow> ('a, 'b) projLine \<Rightarrow> bool)" where
      "projectivize meets (Ordinary P) (OrdinaryL l) = meets P l" 
    | "projectivize meets (Ideal l) (OrdinaryL m) = affine_plane_data.parallel UNIV UNIV meets l m"
    | "projectivize meets (Ordinary P) Infty = False"
    | "projectivize meets (Ideal l) Infty = True"

  datatype ppts = Ppt | Qpt | Rpt | Spt | PQinf | PRinf | PSinf
  datatype plns = PQln | PRln | PSln | QRln | QSln | RSln | LAI
  fun pmeets :: "ppts \<Rightarrow> plns \<Rightarrow> bool" where
    "pmeets Ppt PQln = True" |
    "pmeets Qpt PQln = True" |
    "pmeets PQinf PQln = True" |

    "pmeets Ppt PRln = True" |
    "pmeets Rpt PRln = True" |
    "pmeets PRinf PRln = True" |

    "pmeets Ppt PSln = True" |
    "pmeets Spt PSln = True" |
    "pmeets PSinf PSln = True" |

    "pmeets Qpt QRln = True" |
    "pmeets Rpt QRln = True" |
    "pmeets PSinf QRln = True" |

    "pmeets Qpt QSln = True" |
    "pmeets Spt QSln = True" |
    "pmeets PRinf QSln = True" |

    "pmeets Rpt RSln = True" |
    "pmeets Spt RSln = True" |
    "pmeets PQinf RSln = True" |

    "pmeets PQinf LAI = True" |
    "pmeets PRinf LAI = True" |
    "pmeets PSinf LAI = True" |


    "pmeets Rpt PQln = False" |
    "pmeets Spt PQln = False" |
    "pmeets PRinf PQln = False" |
    "pmeets PSinf PQln = False" |

    "pmeets Qpt PRln = False" |
    "pmeets Spt PRln = False" |
    "pmeets PQinf PRln = False" |
    "pmeets PSinf PRln = False" |

    "pmeets Qpt PSln = False" |
    "pmeets Rpt PSln = False" |
    "pmeets PQinf PSln = False" |
    "pmeets PRinf PSln = False" |

    "pmeets Ppt QRln = False" |
    "pmeets Spt QRln = False" |
    "pmeets PQinf QRln = False" |
    "pmeets PRinf QRln = False" |

    "pmeets Ppt QSln = False" |
    "pmeets Rpt QSln = False" |
    "pmeets PQinf QSln = False" |
    "pmeets PSinf QSln = False" |

    "pmeets Ppt RSln = False" |
    "pmeets Qpt RSln = False" |
    "pmeets PRinf RSln = False" |
    "pmeets PSinf RSln = False" |

    "pmeets Ppt LAI = False" |
    "pmeets Qpt LAI = False" |
    "pmeets Rpt LAI = False" |
    "pmeets Spt LAI = False" 

  text \<open>Show that pmeets satisfies the projective plane axioms: \jackson \<close>

(* all of these can be proved by maaaany cases ... *)
lemma "pmeets_p1": "\<forall>P Q. P \<noteq> Q \<longrightarrow> (\<exists>!l. pmeets P l \<and> pmeets Q l)"
  sorry
lemma "pmeets_p2": "\<forall>l m. l \<noteq> m \<longrightarrow> (\<exists>!P. pmeets P l \<and> pmeets P m)"
  sorry
lemma "pmeets_p3": "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> projective_plane_data.collinear UNIV UNIV pmeets P Q R"
  by (smt pmeets.simps(1) pmeets.simps(24) pmeets.simps(3) pmeets_p2 ppts.distinct(8) projective_plane_data.collinear.elims)
lemma "pmeets_p4": "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> pmeets P l \<and> pmeets Q l \<and> pmeets R l"
  sorry

theorem "projective_plane UNIV UNIV pmeets"
  unfolding projective_plane_def
  using pmeets_p1 pmeets_p2 pmeets_p3 pmeets_p4 by auto

text \<open>\done\<close>

(*
theorem projectivization_p1: "\<lbrakk>P \<noteq> Q; affine_plane meets; pm = projectivize meets\<rbrakk> \<Longrightarrow>  \<exists>l. pm P l \<and> pm Q l"
sorry 
*)

end


