# Positive density of Collatz convergence at every rate above \(3/\log(4/3)\)

## Abstract

We prove that a single positive lower natural-density constant bounds the
proportion of positive integers reaching \(1\) within \(c\log x\) ordinary
Collatz steps for every fixed \(c>3/\log(4/3)\). For each fixed positive target
coprime to three, the same range of clocks holds with a target-dependent
constant, irrespective of its subsequent orbit. The proof constructs weighted
inverse trajectories from a fixed finite family of roots and preserves a
positive weighted mass at every sufficiently large scale. We derive an
explicit primitive Fourier-decay estimate using the exact binomial
first-passage law of paired geometric valuations. At order \(6409\), its
coefficient \(C\) satisfies \(\log_2\log_2\log_2 C<176\), compared with
\(>2^{172}\) for the coefficient specified in [3]. This estimate controls
the variation of the root weights and their transfer to integer sources.
A product inequality for all real moment orders \(p\ge1\) propagates finite
reference-density bounds; direct \(3/2\)-moment certificates and complementary
residue capacity give explicit density estimates after harmonic and dyadic
counting. A residue-completion construction increases the root score while
preserving the indexed root-to-one clocks. Finally, diagonalization gives a
single positive-density set with an unspecified vanishing loss above the
limiting clock.

## Introduction and main results

### Ordinary hitting times and lower density

Write \(\mathbb N=\{1,2,3,\ldots\}\). The ordinary Collatz map is
\[
 \operatorname{Col}(x)=
 \begin{cases}
  x/2,&x\text{ even},\\
  3x+1,&x\text{ odd}.
 \end{cases}
\]
The Collatz conjecture asserts that every positive integer eventually reaches
\(1\). Throughout this paper, convergence means reaching \(1\), and each
application of \(\operatorname{Col}\) counts as one step.

For a positive target \(y\), let \(\tau_y(x)\) be the least nonnegative
integer \(j\) such that \(\operatorname{Col}^j(x)=y\), with
\(\tau_y(x)=\infty\) when there is no such \(j\). All unmarked logarithms
are natural, and \(\log_2\) denotes base two. Put
\[
 c_0=\frac3{\log(4/3)},\qquad
 \mathcal G_c(y)=\{x\ge1:\tau_y(x)\le c\log x\},\qquad
 \mathcal G_c=\mathcal G_c(1).
\]
The notation
\[
 \mathcal G=\{x\ge1:\tau_1(x)\le(10431/1000)\log x\}
\]
is used for the fixed numerical specialization. For \(S\subseteq\mathbb N\),
its lower natural density is
\[
 \underline d(S)=\liminf_{X\to\infty}\frac{\#(S\cap[1,X])}{X}.
\]
Our results count both even and odd integers and give lower bounds at every
sufficiently large cutoff.

### Main results

**Theorem (positive density at every rate above \(c_0\)).** There is an
explicitly computable constant \(c_*>0\) such that, for every real
\(c>c_0\),
\[
 \liminf_{Y\to\infty}\frac1Y
 \#\{x\in\mathbb N:x\le Y,\ \tau_1(x)\le c\log x\}
 \ge c_*>0.                                           \tag{I.main}
\]

The constant \(c_*\) is independent of \(c\). For each fixed \(c>c_0\) and
\(0<d<c_*\), the proportion is at least \(d\) at every sufficiently large
cutoff; that cutoff may depend on \(c\) and \(d\). The finite certificates
and terminating optimization defining \(c_*\) are given in
(D.densityrecipe).

The ratio \(c_0\approx10.42817849\) arises from geometric valuations with
\(\Pr(K=k)=2^{-k}\), \(k\ge1\). One accelerated odd step has mean ordinary
cost \(1+\mathbb EK=3\) and mean logarithmic contraction
\(\mathbb EK\log2-\log3=\log(4/3)\). Related stochastic stopping-time
models are surveyed in [5]. The exact stopped means (S.means) and the
weighted inverse construction connect this ratio to the counting theorem.
The [endpoint discussion](#endpoint_scope) describes the role of the
strict inequality \(c>c_0\).

**Theorem (every fixed target coprime to three).** For every positive
integer \(y\) with \(3\nmid y\), there is an effectively defined \(d_y>0\)
such that
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c(y))\ge d_y.                 \tag{I.targets}
\]
The estimate applies irrespective of the orbit after the target is reached.
Its constant is fixed before \(c\). The [fixed-target construction](#fixed_targets) gives the
root-score recipe and its one-period refinement (D.oneperiodscore).
The restriction on \(y\) is exact: when \(3\mid y\), its predecessor basin
is \(\{2^j y:j\ge0\}\), which has natural density zero. Disjoint predecessor
basins also preclude a positive constant uniform over all admissible targets.

An elementary maximum estimate gives the common-clock result without the
large finite moment tables:
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c)\ge d_{\rm qual}>0.        \tag{I.qualitative}
\]
Both the root score and the coarse residue level in (D.elementarydensity)
are chosen before \(c\). The qualitative argument can also use Tao's
reference-law mixing estimates [1]. The common density has the diagonal
consequence (D.vanishingclock): there is one positive-density set on which
\(\tau_1(x)\le(c_0+\eta(x))\log x\) for a nonincreasing
\(\eta(x)\to0\).

### Root scores and explicit density bounds

The construction begins with a finite family of odd *roots* with specified
paths to the target. A reference distribution modulo powers of three assigns
a marker to each inverse trajectory. A *root score* \(W>0\) is a guaranteed
sum of persistent marked weights, each divided by its root. Sections 7–8
construct the baseline rational score \(W_*\in(0,2^{-4096}]\).

There are four density estimates for a given score. The formula
\(c_{\rm MV}(W)\) uses maximum and centered second-moment bounds;
\(c_{\rm FM}(W)\) adds a direct \(3/2\)-moment with twelve-step propagation;
\(c_{{\rm FM},16}(W)\) also uses sixteen-step propagation; and
\(c_{\rm comp}(W)\) uses complementary residue capacity. Section 10 defines
these functions by optimization over the coarse residue level, with a common
mixing envelope and counting conversion.

For every \(0<W\le2^{-4096}\), writing \(a=\log_2(1/W)\), we prove
\[
 \frac{c_{\rm FM}(W)}{c_{\rm MV}(W)}
 >
 2^{\,2^{(a-9)/95}/1000-2a-31}>2.                     \tag{I.gain}
\]
At the same score, (Q.sixteengain) gives
\(c_{\rm comp}(W)>c_{{\rm FM},16}(W)>(1369/625)c_{\rm FM}(W)\).
These comparisons concern the complete optimized lower-bound formulas.
Their absolute size is estimated in Section 11.

**Quantitative refinement of the root pool.** The residue-completion
construction in [Appendix C](#appendix_roots) supplies a score
\(W_{\mathcal F}^{\rm joint}=W_{\mathcal F}^{\rm joint}(q_N,P)\), where
\(q_N\) and \(P\) are the startup level and residual mass from
(R.residual)–(R.score). It satisfies
\[
 W_{\mathcal F}^{\rm joint}>\mathfrak A_bW_*,
 \qquad
 \mathfrak A_b=2.9273409933\ldots\times10^{275},
 \qquad b=2^{25}.                                    \tag{I.rootgain}
\]
For comparisons within the twelve-step formula, define
\[
 \begin{aligned}
 c_*&:=c_{\rm FM}(W_*),\\
 c_{\rm amp}&:=c_{\rm FM}(\mathfrak A_bW_*),\\
 c_{\rm joint}&:=c_{\rm FM}(W_{\mathcal F}^{\rm joint}).
 \end{aligned}
                                                        \tag{I.constants}
\]
The combined density bound is
\[
 \begin{aligned}
 \underline d(\mathcal G_c)&\ge c_{\rm comp}(W_{\mathcal F}^{\rm joint})\\
                         &>c_{\rm joint}>c_{\rm amp}>c_*>0
                           \qquad(c>c_0).
 \end{aligned}                                        \tag{I.rootdensity}
\]
The first comparison follows from (Q.sixteengain), and the remaining ones
from (Q.cubicscore) and (C.domainguard). All constants are independent of \(c\).
The root construction redistributes valuations along fixed trajectories and
subtracts their sum from the incoming inverse step. This preserves the total
ordinary clock for each seed and index. Backward residue completion and
prefix-height estimates produce residue-complete nonrecurrent root blocks.

### The counting mechanism

Exact affine formulas identify the valuation words that give positive integer
trajectories. After normalization by the roots and identification of repeated
representations, the aggregate weight of a source \(x\) is at most \(1/x\).
Thus source weight \(u\) in \([X,\Lambda X)\) already requires at least
\(uX\) distinct integers. Harmonic allocation and counting their disjoint
dyadic towers give the sharper conversion used in Section 10.

The analytic step bounds primitive Fourier coefficients of the reference law.
Appendix E derives an explicit coefficient using the original pair process,
its binomial first-passage law, and separated phase triangles. Section 6
converts this estimate into all-level mixing with exponent \(2314/25\) and
coefficient \(C_6=2C_{\rm primitive}20^{6409}+2\). This controls the total
variation of the root marks and the error in passing to a fixed coarse level.

Splitting a reference word gives a mixture of affine permutations. Jensen's
inequality therefore bounds a moment at a combined level by the product of
the moments at the two component levels, for every real order \(p\ge1\).
The finite direct \(3/2\)-moment certificates extend to all levels through
this product inequality. Hölder's inequality, applied to both occupied and
complementary residue capacity, converts marked mass into source mass.

For example, the second-moment bound \(M_2(12)\le6.803\) and mean one give
\(M_{3/2}(12)\le\sqrt{6.803}\approx2.608256\), whereas direct calculation
gives \(M_{3/2}(12)\le2.113605\). The counting denominators from the
second-moment block at sixteen and fractional block at twelve have rates
\[
 8.685^{1/16}\approx1.14465106,\qquad
 2.113605^{1/6}\approx1.13284538.
\]
The slower growth of the latter compensates for its extra power of the
residual marked mass, as (I.gain) shows. The direct depth-sixteen fractional
certificate further reduces its denominator rate to \(1.10650942918\ldots\).

The seed words have exact depth \(b_j\) and total valuation in
\([2b_j-\lceil b_j^{3/5}\rceil,2b_j+\lceil b_j^{3/5}\rceil]\).
Their reference survival is at least \(24/25\). A summable variation bound
then supplies a fixed positive root score. Varying the continuation and
terminal parameters gives every fixed \(c>c_0\) with this same score;
\(10431/1000=10.431\) is one numerical specialization.

### Relation to previous work

Krasikov and Lagarias [6] use difference inequalities and a computer-assisted
argument to obtain at least \(X^{0.84}\) predecessors below \(X\) for each
fixed positive target coprime to three, once \(X\) is sufficiently large.
Tao [1] proves that the minimum of a Collatz orbit is below any prescribed
function tending to infinity for almost all starting integers in logarithmic
density. His proof develops the reference-law and Fourier methods used here.

Mazur [3] obtains convergence to \(1\) within \((523/50)\log x\) ordinary
steps on a set of positive lower natural density, with an explicit finite
cutoff. We build on his weighted inverse-trajectory and terminal-counting
framework. The analytic and trajectory estimates used in our density proof
are derived in this paper, including the primitive Fourier bound in Appendix E.
The pairing and separated-triangle method follows Tao [1, Section 7] and its
explicit development in [3]; our first-passage calculation works directly with
the original pair process and supplies the coefficient used throughout.

The main clock result gives one density constant for every fixed
\(c>3/\log(4/3)\). The moment estimates, complementary capacity, and root
completion provide its quantitative refinements. Section 11 compares their
formulas with the bound in [3], including its distinct finite-cutoff recipe.
Appendix A compares the two seed constructions at a common analytic coefficient.

Mazur [4] also proves positive lower natural density of predecessors for each
fixed positive target coprime to three. Theorem (I.targets) supplies ordinary
hitting times throughout \(c>c_0\), with one effective target-dependent
constant. Its root construction applies independently of the orbit after the
target is reached.

### Terminology and recurring notation {#notation_overview}

A *source* is a starting integer being counted, a *target* is the integer to
be reached, and a *root* is a selected odd intermediate integer with a
specified finite path to that target. A *valuation word* records the positive
numbers of halvings between successive odd states. The finite initial word
families form the *seed*. A *graft* is the finite transition to the stopped
blocks used to continue the inverse trajectories.

A *persistent mark* is a lower bound valid at every later stage. Its weighted
sum, rather than each individual mark, is positive. A *residue-complete block*
has one root in every unit residue class at the chosen modulus; *unit* means
coprime to three. A root family is *nonrecurrent* when no positive accelerated
iterate of a member belongs to the family, including the same member.

| Notation | Meaning |
|---|---|
| \(\operatorname{Col},\tau_y(x)\) | Ordinary Collatz map and first hitting time; an odd step and every halving are counted separately. |
| \(c,c_0\) | Ordinary-step coefficient and the ratio \(3/\log(4/3)\). |
| \(c_*,c_{\rm amp},c_{\rm joint}\) | Density constants in (I.constants). |
| \(G_q,\mathcal U_q\) | All residues and unit residues modulo \(3^q\). |
| \(f_q,\rho_q,H_q\) | Mean-one reference density, its rescaling \((2/3)f_q\), and the reference fan. |
| \(W,W_*\) | A root score and the baseline score. |
| \(c_{\rm MV},c_{\rm FM},c_{{\rm FM},16},c_{\rm comp}\) | Maximum/variance, twelve-step fractional, sixteen-step fractional, and complementary-capacity density formulas. |
| \(m,k(X)\) | Fixed coarse residue level and finer level growing with the cutoff. |

Symbols confined to a construction have local meanings. The schedule
coefficient \(L\) in Sections 3–5 is distinct from \(L=2\log2\) in counting;
the seed sizes \(b_j\) are distinct from the growing terminal size \(b\);
and the accelerated map \(U\) in Section 1 is distinct from the source mass
\(U\) in Section 10. Local notation tables accompany the terminal and
counting arguments.

### Proof architecture and order of choices {#proof_architecture}

The argument passes from analytic mixing to persistent root scores, then to
integer source families and density:
\[
 \begin{array}{c}
 \text{Primitive Fourier decay (Appendix E)}\\
 \downarrow\\
 \text{Reference mixing and a fixed persistent root score}\\
 \downarrow\\
 \text{Source families at every large scale, for each }c>c_0\\
 \swarrow\qquad\searrow\\
 \text{Elementary maximum bound}\qquad\text{Direct moment bounds}\\
 \searrow\qquad\swarrow\\
 \text{Harmonic and dyadic counting}\\
 \downarrow\\
 \text{Positive lower natural density}.
 \end{array}
\]
The [quantitative reduction](#quantitative_reduction) states the source-family
theorem and counting estimates first. Sections 1–2 establish the exact word
identities and transfer bounds. Sections 3–5 construct all-scale sources from
mixing and persistent-root estimates, proved in Sections 6–8. Sections 9–10
give the moment and counting arguments, and Section 11 compares their explicit
bounds. The forward references from the construction are thus discharged
before its final application.

Appendix A compares fixed-depth and first-crossing seeds. Appendix B proves
monotonicity in the analytic coefficient. [Appendix C](#appendix_roots)
establishes the root refinement; [Appendix D](#appendix_reference_consequences)
develops concentration-profile and entropy consequences. [Appendix E](#appendix_primitive_local)
contains the primitive-decay proof required for the explicit theorem.

The analytic coefficient, seed, finite root pool, and moment certificates are
fixed first. The root score and mixing envelope determine the coarse counting
level, independently of the clock. Next choose \(c>c_0\), its positive
terminal parameter, an error tolerance, and a finite graft. The counting
cutoff then tends to infinity. The root pool and graft remain fixed while the
terminal trajectories and their precision grow. The final counting argument
uses finitely many disjoint intervals before taking its remaining limits.

## From source families to density {#quantitative_reduction}

This section isolates the estimates used in counting. The intervening
construction will supply the source families in the theorem below; its
proof can be read after the quantitative purpose of those families is clear.

### The reference distribution and source-family theorem

For an integer \(m\ge0\), let \(G_m=\mathbb Z/3^m\mathbb Z\), and
write \(\langle h\rangle_m=3^{-m}\sum_{r\in G_m}h(r)\).
Take independent positive integers \(K_i\) with
\(\Pr(K_i=a)=2^{-a}\), and put \(S_i=K_1+\cdots+K_i\).
The reference law \(\mu_m\) is the distribution of
\(\sum_{i=1}^m3^{i-1}2^{-S_i}\) in \(G_m\), where powers of two
are inverted modulo \(3^m\). Its density relative to the uniform measure
is \(f_m(r)=3^m\mu_m(r)\), and \(\rho_m=(2/3)f_m\).
The empty sum gives \(f_0=1\). Section 2 relates this reference law to
weighted integer trajectories by exact affine transfer identities.

The weighted sum needed after reducing terminal trajectories is
\[
 F_j(x)=4^jx+(4^j-1)/3,\qquad
 H_m(x)=\sum_{j\ge0}4^{-j}\rho_m(F_j(x)).
\]
We call this sum the reference fan. Each \(F_j\) permutes \(G_m\),
so \(\langle H_m\rangle_m=8/9=:\mu\). The
[reference-moment section](#chapter09) proves its exact relation to
\(f_{m+1}\) and its moment estimates.

**Theorem (all-scale source families).** The root construction supplies a
fixed rational score \(W_*>0\). For every fixed \(c>c_0\), every
\(\eta>0\) and every fixed \(\Lambda>16\), a single finite extension
of the construction works at all sufficiently large real \(X\). It gives
a finite odd-source set
\(S_X\subseteq\mathcal G_c\cap[X,R_XX)\), weights \(0\le a_x\le1/x\),
and an integer \(k(X)\), such that
\[
 W_*-\eta\le\sum_{x\in S_X}a_xH_{k(X)}(x),\qquad
 R_X<\Lambda,\quad R_X\longrightarrow16,\quad
 k(X)\longrightarrow\infty,\quad 3^{k(X)}/X\longrightarrow0.
                                                        \tag{I.sources}
\]
The roots and score are independent of \(c,\eta,\Lambda,X\).

This is (N.everyclock), with the actual radius supplied by (N.selector)
and (N.scales); (R.graftinput) proves its root and mixing premises.
The score is defined by the finite recipe (R.score).

### General moments give lower bounds for physical source mass

Fix a coarse level \(m\ge2\). Let \(\epsilon_m\) be the mixing-error
envelope (M.envelope), with its explicitly specified positive integer
coefficient \(C_6\). In particular, for every \(n\ge m\),
\[
 \langle|f_n-f_m\circ\pi_{n,m}|\rangle_n\le\epsilon_m
 \le C_6m^{-2314/25},
\]
where \(\pi_{n,m}\) is reduction from \(G_n\) to \(G_m\).
Put \(L=2\log2\), \(\kappa=(8/9)L\), and
\(p_m=(W-\kappa\epsilon_m)_+\), where \(t_+=\max\{t,0\}\)
and \(W\) is a score for which the source-family conclusion holds.

For \(s>1\), suppose \(B_{s,m}\ge\langle H_m^s\rangle_m\).
The total source mass \(U=\sum_xa_x\) then has the limiting lower bound
\[
 v_{s,m}(W)=
 \frac{p_m^{s/(s-1)}}{(LB_{s,m})^{1/(s-1)}}.          \tag{I.generalp}
\]
More precisely, every strict smaller nonnegative mass is available at
every sufficiently large scale, after fixing the error allowance.

Here is the key inequality. With \(Q=3^m\), the actual residue masses
\(w_r=\sum_{x\equiv r\ (Q)}a_x\) obey
\[
 w_r\le\frac{T_X}{Q},\qquad
 T_X=\frac QX+\frac12\log R_X\longrightarrow L.
\]
Indeed, odd representatives in a residue class have spacing \(2Q\).
Weighted Hölder therefore gives
\[
 \sum_rw_rH_m(r)
 \le U^{1-1/s}\left(\sum_rw_rH_m(r)^s\right)^{1/s}
 \le U^{1-1/s}(T_XB_{s,m})^{1/s}.
\]
The fine-to-coarse error tends to at most \(\kappa\epsilon_m\).
Taking limits with \(m,s\) fixed yields (I.generalp). The proof of
(D.generalp) below supplies the precise tolerance and all-scale quantifiers.
The finite-cutoff estimates use \(T_X\); their limiting coefficient is \(L\).

Distinct odd sources have disjoint sets of multiples by powers of two,
and these multiples remain in \(\mathcal G_c\), since \(c\log2>1\). Keeping their weights
while counting gives the conversion
\[
 \mathcal D(u)=\frac{32}{225}(e^{2u}-1),\qquad
 0\le u\le\tfrac12\log(3/2),\qquad
 \underline d(\mathcal G_c)\ge\mathcal D(u).            \tag{I.conversion}
\]
Here \(u\) must be available in every sufficiently late interval of every
fixed ratio greater than sixteen. The proof is (D.radial).
For the constructed range \(0<W\le27/2^{27}\), all mass bounds used
here lie within this domain.

At \(s=3/2\), the direct certificate gives
\(B_{3/2,m}=\mathcal B_m\), where
\(\mathcal B_m^2\le5(57/50)^m\), and (I.generalp) is
\(p_m^3/(L^2\mathcal B_m^2)\). The formula \(c_{\rm FM}(W)\)
retains the maximum of this branch and the maximum/variance branches,
then optimizes the coarse level using the same conversion \(\mathcal D\).
Thus each of the long construction's inputs has a specific role:
the root score supplies marked mass, mixing bounds the error in changing level,
and concentration bounds force enough actual source mass to be counted.

**Corollary (a simple rational density bound).** For a rational source-family
score \(0<W\le27/2^{27}\), define
\[
 m_\circ=\max\left\{2,\left\lceil
             \left(\frac{5C_6}{2W}\right)^{25/2314}
                         \right\rceil\right\}.
\]
Then
\[
 \underline d(\mathcal G_c)\ge c_{\rm FM}(W)>
 \frac4{1125}W^3\left(\frac{57}{50}\right)^{-m_\circ}.
                                                        \tag{I.rational}
\]
The choice gives \(p_{m_\circ}>W/2\); (D.explicit) proves the remaining
constants and the integer-power recipe for \(m_\circ\).
This convenient rational bound is weaker than the optimized formula.
In particular it applies to \(W=W_*\), giving an explicit lower bound
without first carrying out the full optimization.

## 1. Exact valuation words and physical trajectories {#chapter01}

We first relate a finite list of valuations to a congruence class of
trajectories and an exact affine formula. Reversing that formula constructs
predecessors of a known convergent integer. The resulting weight bound,
after histories with the same starting integer are combined, will be the
input to the final count.

For a prime \(p\) and a positive integer \(n\), write \(\nu_p(n)\)
for the largest integer \(a\ge0\) such that \(p^a\) divides \(n\).

Let \(U(x)=(3x+1)/2^{\nu_2(3x+1)}\) on positive odd integers. An ordinary
Collatz step sends odd \(x\) to \(3x+1\), and even \(x\) to \(x/2\).
One \(U\)-step of valuation \(k\) comprises \(k+1\) ordinary steps.

### Exact local certificates

For a word \(w=(k_1,\ldots,k_d)\) of positive integers, put
\[
 S_j=\sum_{i\le j}k_i,\quad S_0=0,\qquad
 B_0=0,\quad B_j=3B_{j-1}+2^{S_{j-1}}.                  \tag{W.data}
\]
A certificate \(\operatorname{WordCert}(r,E,w)\) consists of a positive
odd representative \(r\), an integer \(E\ge S_d+1\), and the finite
checks \(\nu_2(3U^{j-1}(r)+1)=k_j\) for \(1\le j\le d\). An empty
word is allowed, with \(E\ge1\).

Here a *source* is the starting integer of the forward trajectory, and its
*endpoint* is the value reached after the word. The congruence condition
\(x\equiv r\pmod{2^E}\) is called a *cylinder*. Specifying a value to
\(e\) bits of precision means fixing its residue modulo \(2^e\).

**Theorem (word invariance, affine endpoint, and precision).** Every positive
\(x\equiv r\pmod{2^E}\) has exactly the certified word and satisfies
\[
 U^j(x)=\frac{3^jx+B_j}{2^{S_j}}\quad(0\le j\le d).      \tag{W.affine}
\]
For \(x=r+2^Eh>0\),
\[
 U^d(x)=U^d(r)+3^d2^{E-S_d}h.                           \tag{W.output}
\]
The guaranteed output precision is \(E-S_d\) bits, and cannot uniformly be
increased by one bit on this entire cylinder. If \(2^{S_d}>3^d\), descent
holds for every such source with \(x>B_d/(2^{S_d}-3^d)\). The word takes
exactly \(S_d+d\) ordinary steps.

*Proof.* Suppose the two trajectories agree in valuations through step
\(j-1\). Their next pre-division numerators differ by
\(3^j(x-r)/2^{S_{j-1}}\), divisible by \(2^{E-S_{j-1}}\). Since
\(E-S_{j-1}\ge k_j+1\), this does not change the known valuation
\(k_j\). Division gives the next affine formula and difference, completing
induction. The coefficient of \(h\) in (W.output) has exact valuation
\(E-S_d\), since \(3^d\) is odd. Two consecutive sufficiently large
nonnegative \(h\)'s give positive sources and endpoints differing by that
valuation, so no stronger uniform precision is possible. Descent is exactly
\((2^{S_d}-3^d)x>B_d\). Summing \(k_j+1\) gives the clock. \(\square\)

**Lemma (one source cylinder per word).** Every positive valuation word is
realized by exactly one odd residue class modulo \(2^{S_d+1}\). That
cylinder has Haar probability \(2^{-S_d}\) among odd 2-adic integers.

In finite terms, exactly one of the \(2^{S_d}\) odd residue classes
modulo \(2^{S_d+1}\) realizes the word. Haar probability assigns equal mass to these classes.

*Proof.* The empty word is the odd class modulo two. Suppose a prefix of
total valuation \(S\) has its unique class modulo \(2^{S+1}\). By
(W.output), refining it modulo \(2^{S+k+1}\) makes its current endpoint
run bijectively over odd residues modulo \(2^{k+1}\), because the variable
coefficient is twice a unit. Exactly one residue obeys
\(3y+1\equiv2^k\pmod{2^{k+1}}\), the condition for valuation \(k\).
That residue is odd, and the selected source class has positive
representatives. Induction proves existence and uniqueness. The product of
the successive Haar fractions \(2^{-k}\) is \(2^{-S_d}\). The later counting argument uses the actual weights of integer sources. \(\square\)

### Orientation and affine composition

An inverse word \((k_1,\ldots,k_d)\) attached to an odd root \(M\)
means
\[
 x_0=M,\qquad x_i=(2^{k_i}x_{i-1}-1)/3.                 \tag{W.inverse}
\]
It is physically realized when every \(x_i\) is positive, odd, and integral.
We use *physical* only to distinguish these actual integer trajectories
from the auxiliary residue-class calculations introduced later.
Then \(U(x_i)=x_{i-1}\), and the chronological forward word from \(x_d\)
is \((k_d,\ldots,k_1)\), not the displayed inverse order. Direct
substitution gives
\[
 M=3^d2^{-S_d}x_d+C_w,\qquad
 C_w=\sum_{i=1}^d3^{i-1}2^{-S_i}.                       \tag{W.offset}
\]
The totals \(S_d,d\) and the clock \(S_d+d\) are reversal invariant;
prefix tests and additive offset formulas are not.

*Proof.* Solve the next inverse step as
\(x_{i-1}=3\,2^{-k_i}x_i+2^{-k_i}\). Substitution into
\(M=3^{i-1}2^{-S_{i-1}}x_{i-1}+C_{i-1}\) adds
\(3^{i-1}2^{-S_i}\) to the offset and gives the next slope. Induction
proves (W.offset). Oddness of \(x_{i-1}\) in
\(3x_i+1=2^{k_i}x_{i-1}\) proves the valuation is exactly \(k_i\).
\(\square\)

If \(M=\omega_1y+C_1\) and \(y=\omega_2x+C_2\), then
\[
 M=\omega_1\omega_2x+C_1+\omega_1C_2.                  \tag{W.compose}
\]
This composition formula will be used when new inverse blocks are attached
to a finite history. It retains the order of the blocks and their offsets.

### Convergent roots and uniqueness of source weights

The *pre-1 odd basin* of a root consists of the odd integers whose forward
trajectory visits that root before reaching one. A family of words is
*prefix-free* if no selected word is a proper initial segment of another.
*Parsing* a concatenation means identifying the cuts between its component
words. These two properties will prevent a trajectory from being counted
more than once.

For \(s\ge1\), let \(R_s=(4^s-1)/3\). It is positive and odd,
\(3R_s+1=2^{2s}\), and \(U(R_s)=1\). For \(s>1\), its first
ordinary hitting time of one is \(2s+1\); \(R_1=1\) has hitting time
zero. Distinct \(R_s>1\) have disjoint pre-1 odd basins: after visiting
one of them a trajectory has next odd value one, where it remains. It
cannot visit another root, or visit the same root twice before reaching one.

A physically realized complete history ending at \(R_s>1\), with source
\(x\) and physical weight \(\omega=3^d2^{-S_d}\), satisfies
\[
 x\omega\le R_s                                       \tag{W.charge}
\]
by the nonnegative offset in (W.offset). Under a deterministic prefix-free
stopping/parsing rule, a source and root admit at most one complete retained
history: the orbit and valuations are unique, the root is visited at most
once, and parsing has no choice. Thus the same weight bound applies after grouping
by actual source, provided compression preimages have first been identified
rather than counted as additional reduced histories.

Normalize the weight at root \(R_s\) by dividing by \(R_s\), and pool
distinct such roots. Basin disjointness gives the aggregate weight bound
\(a_x\le1/x\), not one copy of that bound per root. The later
terminal-compression proof must establish unique reduced-history parsing
before invoking this conclusion.

**Lemma (source weights for a nonrecurrent root family).** Let \(\mathcal P\) be a finite
set of distinct positive odd roots such that
\[
 U^j(M)\ne L
 \quad(M,L\in\mathcal P,\ j\ge1),                    \tag{W.antichain}
\]
including \(M=L\). Then a source visits the pool at most once. Under the
same deterministic parsing and identification of compression preimages,
\[
 a_x=\sum_{M\in\mathcal P}\frac1M
          \sum_{\substack{z\ {\rm reduced\ from}\ M\\x_z=x}}\omega_z
 \le\frac1x.                                         \tag{W.poolcharge}
\]
Indeed, two visits in chronological order would violate (W.antichain).
The single visit fixes its valuation word and its parsed history, and
\(x\omega_z\le M\) follows from (W.offset). Distinct convergent roots form
such a pool whenever none is a forward iterate of another; a root greater
than one that reaches one cannot recur. The nonrecurrence condition is imposed on the actual orbit. \(\square\)

**Lemma (one-step roots of an arbitrary odd unit).** For \(y>0\) odd,
\(3\nmid y\), define
\[
 e(y)=\begin{cases}2,&y\equiv1\pmod3,\\1,&y\equiv2\pmod3,\end{cases}
 \qquad
 X_t(y)=\frac{2^{2t+e(y)}y-1}{3}\quad(t\ge0).          \tag{W.constructor}
\]
These are precisely the positive odd predecessors of \(y\), without
repetition, with exact valuation \(2t+e(y)\). Integrality determines the
parity of that valuation, and \(3X_t(y)+1=2^{2t+e(y)}y\) proves the
claim. There is no odd predecessor when \(3\mid y\).
With \(R_0=0\), one also has
\(X_t(y)=2^{e(y)}yR_t+(2^{e(y)}y-1)/3\).
For \(q\ge1\), the multiplier is invertible modulo \(3^q\), so the root-period proof in
Section 2, which also applies to nonnegative indices, shows that every
\(3^q\) consecutive \(t\)'s give every residue once. Filtering out
nonunits retains exactly \(2\cdot3^{q-1}\) roots. \(\square\)

**Lemma (removing a possible cycle predecessor).** For any function \(F\)
and fixed \(y\), at most one \(z\) with \(F(z)=y\) is periodic. The
nonperiodic points in that fiber satisfy the analogue of (W.antichain).
A periodic predecessor puts \(y\) on its cycle, where there is exactly
one cyclic predecessor of \(y\). If \(F^j(z)=w\), \(j>0\), for two
predecessors, then \(F^j(y)=y\) and \(w=F^{j-1}(y)\); thus \(w\) is
periodic. This also rules out recurrence of one nonperiodic predecessor.
 \(\square\)

**Corollary (the complete finite-depth hierarchy).** Define
\[
 \mathcal C_0=\{1\},\qquad
 \mathcal C_{d+1}
 =\{X_t(y):y\in\mathcal C_d,\ 3\nmid y,\ t\ge0,\ X_t(y)>1\}.
 \tag{W.depthclasses}
\]
Then \(\mathcal C_d\) is exactly the set of positive odd integers with
first accelerated hitting time \(d\) to one. Induct on \(d\), using
(W.constructor) and uniqueness of the next odd value. Excluding one
prevents extending its cycle, and \(3\mid y\) supplies no predecessors.
For \(d\ge1\), different members of \(\mathcal C_d\) cannot lie on
one another's forward orbit: such a visit would strictly decrease the
remaining first-hitting depth. Thus every finite subset is an antichain.
The hierarchy exhausts finite convergent odd trajectories, without
asserting that every odd integer belongs to a finite level.

## 2. Reference transfer and capacity of physical histories {#chapter02}

The word formulas now connect actual trajectories to the auxiliary residue
distribution of [1, 2]. The affine transfer follows [3, §2], and the
selected-family comparison follows [3, §3]. We give their proofs with the
word orientation and normalization used here, then bound the total
trajectory weight in each residue class. These capacity bounds will
compare weighted sums with the reference distribution. The quantitative
mixing estimate is stated here and proved in the later mixing section.

### The reference law and its normalization

Write \(G_q=\mathbb Z/3^q\mathbb Z\), including the one-point group \(G_0\),
and \(\langle f\rangle_q=3^{-q}\sum_{y\in G_q}f(y)\). A dyadic rational
has an unambiguous image in every \(G_q\): a fraction with denominator a
power of two is evaluated using the inverse of that denominator modulo
\(3^q\). At positive levels, the units are the residues not divisible by
three. We call
\(q\) the *ternary residue level* of the modulus \(3^q\).
For \(n\ge m\), let \(\pi_{n,m}:G_n\to G_m\) be reduction modulo
\(3^m\). On an auxiliary probability space
let \(K_i\) be independent with \(\Pr(K_i=a)=2^{-a}\), \(a\ge1\), and put
\(S_i=K_1+\cdots+K_i\). Define

\[
 C_n=\sum_{i=1}^n3^{i-1}2^{-S_i}\pmod{3^n},\quad
 \mu_n(y)=\Pr(C_n=y),\quad f_n=3^n\mu_n,\quad
 \rho_n=\frac23 f_n.                                  \tag{T.law}
\]

Thus \(f_0=1\) and \(\rho_0=2/3\). This normalization is applied once.
The function \(f_n\) is the probability density relative to the uniform
measure on \(G_n\), and \(\rho_n\) is its scaled version. A *marker*
means the numerical factor \(\rho_n(x\bmod3^n)\). To mark a trajectory
weight, multiply it by this factor at the current end of the inverse
construction, which is the source of the corresponding forward trajectory.
Its *marked mass* is the
sum of those products, whereas *unmarked mass* is the sum of the weights
themselves. Markers are not indicator functions.
In particular \(\langle f_n\rangle_n=1\) and
\(\langle\rho_n\rangle_n=2/3\). For \(n\ge1\) their support consists of
units. Reversing the iid word shows that \(C_n\) has the same law as \(n\)
iterations of \(y\mapsto(3y+1)/2^K\) starting at zero. We use the inverse-
prefix order because its affine offset is exactly the one in (W.offset).

For \(n\ge m\), the first \(m\) terms of \(C_n\) are \(C_m\) and every later
term is zero modulo \(3^m\). Consequently \(\mu_n\) projects to \(\mu_m\).
Equivalently, the average of \(f_n\) over each fiber of \(G_n\to G_m\) is
\(f_m\). This is the projectivity identity for the reference law.

The only analytic premise in this section is a fixed nonnegative envelope
\(\epsilon_m\) satisfying, for every \(n\ge m\ge1\),

\[
 \langle|f_n-f_m\circ\pi_{n,m}|\rangle_n\le\epsilon_m.
                                                               \tag{T.mix}
\]

Section 6 specifies the explicit coefficient and mixing envelope
used in the density formula. The left side is the unhalved L1 distance after uniform lifting, averaged
over the full residue group. For \(\rho\), the distance is multiplied
by \(2/3\).

### One word as an affine injection

Fix an inverse word \(w\) of length \(d\) and total valuation \(A\). Let
\(\omega_w=3^d2^{-A}\) and \(C_w\) be its offset from (W.offset). If \(q\ge d\),
the map

\[
 J_{w,q}:G_{q-d}\longrightarrow G_q,\qquad
 J_{w,q}(z)=C_w+3^d2^{-A}z                              \tag{T.injection}
\]

is well defined and injective. Its image is the single fiber
\(y=C_w\bmod3^d\). Indeed, changing \(z\) by \(3^{q-d}\) changes the
expression by a multiple of \(3^q\), and \(2^{-A}\) is a unit. This also
proves bijectivity onto that fiber. For a real function \(g\) on \(G_{q-d}\),
define

\[
 (\mathcal T_{w,q}g)(y)=
 \begin{cases}
  \omega_w g(J_{w,q}^{-1}(y)),&y\in\operatorname{im}J_{w,q},\\
  0,&\text{otherwise}.
 \end{cases}                                          \tag{T.operator}
\]

**Lemma (exact transfer norms).** This operator is linear and positive, and

\[
 \langle\mathcal T_{w,q}g\rangle_q=2^{-A}\langle g\rangle_{q-d},
 \qquad
 \langle|\mathcal T_{w,q}g|\rangle_q
       =2^{-A}\langle|g|\rangle_{q-d}.                 \tag{T.norm}
\]

*Proof.* Sum over the affine image using its unique preimage. The scaling is
\(3^{-q}\omega_w3^{q-d}=2^{-A}\). Positivity makes the same calculation
valid for absolute values. The empty word gives the identity, including
\(q=0\). \(\square\)

At an odd integer root \(M\), membership in this affine image is equivalent
to integrality of the last inverse endpoint. It also implies integrality of
every earlier endpoint. More explicitly, the inverse recurrence has
denominator \(3^i\) at step \(i\), and the full inverse numerator reduced
modulo \(3^i\) is its step-\(i\) numerator multiplied by the unit
\(2^{A-S_i}\). Each integral endpoint is odd by induction, since the
numerator \(2^{k_i}x_{i-1}-1\) is odd.

Positivity is a separate condition. If \(M>C_w\), then \(M>C_v\) for each
prefix \(v\), because the offset partial sums increase. The identities
\(x_i=(M-C_{w|i})/\omega_{w|i}\) prove every endpoint positive. Under this
condition the value of (T.operator) at \(M\) is exactly the physical inverse
word weight times its endpoint marker. The condition \(M>C_w\) therefore identifies the residue transfer with
positive integer trajectories.

### Prefix-free stopping and its exact deficit

Let \(V\) be a finite prefix-free set of inverse words, each of length at
most \(h\). Set \(p(V)=\sum_{w\in V}2^{-A(w)}\) and \(q=h+k\), where
\(k\ge1\). A length-\(q\) iid word can have at most one prefix in \(V\);
therefore \(p(V)\le1\). Put

\[
 A_{V,q}=\sum_{w\in V}\mathcal T_{w,q}\rho_{q-|w|},\qquad
 L_{V,q,k}=\sum_{w\in V}\mathcal T_{w,q}
                  (\rho_k\circ\pi_{q-|w|,k}).          \tag{T.selected}
\]

**Lemma (selected reference density).** Pointwise \(0\le A_{V,q}\le\rho_q\),
and

\[
 \langle A_{V,q}\rangle_q=
 \langle L_{V,q,k}\rangle_q=\frac23p(V),\qquad
 \langle\rho_q-A_{V,q}\rangle_q=\frac23(1-p(V)).        \tag{T.deficit}
\]

*Proof.* Condition the length-\(q\) iid word on having prefix \(w\).
Its remaining \(q-|w|\) letters are independent geometric variables, and
its offset is \(C_w+\omega_w C_{\rm tail}\). Its contribution to the full
density is therefore \(\mathcal T_{w,q}\rho_{q-|w|}\). The prefix events
are disjoint. Their union gives the selected nonnegative subdensity,
proving the pointwise inequality. Its mean and that of \(L\) follow from
(T.norm) and \(\langle\rho_r\rangle=2/3\). Subtract the means for the last
identity. This also covers \(V\) empty or containing the empty word.
\(\square\)

**Theorem (finite stopping transfer).** For \(1\le\ell\le q\),

\[
 \left\langle\left|L_{V,q,k}-\rho_\ell\circ\pi_{q,\ell}\right|
 \right\rangle_q
 \le\frac23\{p(V)\epsilon_k+\epsilon_\ell+1-p(V)\}
 \le\frac23\{\epsilon_k+\epsilon_\ell+1-p(V)\}.          \tag{T.stopped}
\]

*Proof.* Replace each coarse \(\rho_k\) by \(\rho_{q-|w|}\). The triangle
inequality, (T.norm), and (T.mix) bound the replacement cost by
\((2/3)\epsilon_k\sum_w2^{-A(w)}\). The selected density differs from
\(\rho_q\) by the exact nonnegative deficit in (T.deficit). Finally replace
\(\rho_q\) by the lifted \(\rho_\ell\) at cost \((2/3)\epsilon_\ell\).
The family retains its original reference weights.
\(\square\)

The same statements apply to any fixed subfamily of \(V\). If the family is
chosen differently for different physical parents, this theorem alone does
not control that choice: partition the parents by their chosen family and
pay the comparison for each nonempty group, or prove a different coupling.

### Capacity of actual integer histories

Let \(\mathcal H\) be a finite family of physically realized inverse
histories from a fixed positive odd root \(M\). We call a pair consisting
of the word length and total valuation a *tag*. At most \(T\ge0\) distinct total
tags \((d,A)\) occur. Assume that each history has weight
\(\omega=3^d2^{-A}\le\sigma\), where \(\sigma\ge0\), offset in
\([c_-,c_+]\), where \(c_-\le c_+\), and that within
each tag an integer source supports at most one history. Write
\(C=c_+-c_-\) and

\[
 H_q(a)=\sum_{h\in\mathcal H:\,x_h\equiv a\ (3^q)}\omega_h.
\]

**Theorem (offset-window capacity).** For every \(q\ge0\) and every residue
\(a\),

\[
 3^qH_q(a)\le T(C+3^q\sigma),\qquad
 \left|\sum_aH_q(a)\psi(a)\right|
       \le T(C+3^q\sigma)\langle|\psi|\rangle_q.        \tag{T.capacity}
\]

*Proof.* Fix a tag. Its slope \(\omega\) is constant, and
\(M=\omega x_h+C_h\) confines all sources to an interval of length
\(C/\omega\). Sources in a residue class modulo \(3^q\) have spacing at
least \(3^q\). With no duplicate source within the tag, there are at most
\(1+C/(\omega3^q)\) of them. Multiplication by \(\omega\) bounds their
mass by \(\sigma+C/3^q\). Sum at most \(T\) tags. Pairing the pointwise
bound with \(|\psi|\) proves the second inequality. \(\square\)

Any restriction of \(\mathcal H\) obeys the same bound, without
renormalization. If total depth and valuation are both at most \(S\), one
may take \(T=(S+1)^2\). For \(B\) concatenated blocks of slopes at most
\(\beta\), one may take \(\sigma=\beta^B\). The boundary term \(3^q\sigma\) is retained at every level.

Pairing (T.stopped) with such a parent histogram yields a physical marked
variation bound of

\[
 \frac23T(C+3^q\sigma)
       (\epsilon_k+\epsilon_\ell+1-p(V)).              \tag{T.pairing}
\]

To identify this pairing with an orbit extension, check both integrality and
positivity as above for every selected child. All comparisons remain exact
when the formal residue class contains just one occupied physical source.

### A finite root period

**Lemma (root residues).** For \(q\ge0\), every interval of \(3^q\)
consecutive positive indices \(s\) contains exactly one \(R_s=(4^s-1)/3\)
in each residue modulo \(3^q\). For \(q\ge1\), \(R_s\) is a unit exactly
when \(3\) does not divide \(s\).

*Proof.* For \(t\ge1\),
\(\nu_3(4^t-1)=1+\nu_3(t)\). If \(3\nmid t\), then
\((4^t-1)/3=1+4+\cdots+4^{t-1}\) is \(t\) modulo three. Next, if
\(a\equiv1\pmod3\), then \(a^2+a+1\) has valuation one: writing \(a=1+3z\)
gives \(3(1+3z+3z^2)\). Factoring \(a^3-1\) shows that multiplying \(t\)
by three raises the valuation by one. This proves the formula for all
\(t\). Now \(R_{s+t}-R_s=4^s(4^t-1)/3\) has valuation \(\nu_3(t)\).
Two indices have the same root residue exactly when they agree modulo
\(3^q\). Finally \(R_s\equiv s\pmod3\). \(\square\)

A finite root family can therefore realize a full ternary average exactly.
To use this average uniformly at later stages, we must also control the
total subsequent change of the marks at each fixed root.

## 3. Stopped reference blocks and a global continuation schedule {#chapter03}

The preceding identities apply to any suitable finite word family. We now
construct families by stopping when the affine slope first becomes small
enough. Grouping several stopped words controls both size growth and the
ordinary step count. Crucially, these families depend on the prescribed
block index, not on the integer to which they are attached. Their
probability space is the reference law of (T.law).

### A constant-slope stopping rule

Let \(\lambda=\log_2 3\) and \(\beta=1/8\). For an inverse word \(w\)
define its depth \(d\), total valuation \(A\), displacement \(Y=A-\lambda d\),
and ordinary step count \(R=A+d\). Its slope is \(2^{-Y}\), so the
displacement is the negative base-two logarithm of that slope. Let \(\tau\) be
the first positive depth with \(\sum_{i\le\tau}(K_i-\lambda)\ge3\).
Write \(Y,R\) also for the stopped totals. For integer \(E\ge1\), let
\(V(E)\) consist of first-crossing words with \(A<E\), and set
\(p(E)=\sum_{w\in V(E)}2^{-A(w)}\), \(\varepsilon(E)=1-p(E)\).

The set \(V(E)\) is finite because its positive parts sum to at most \(E-1\),
and prefix-free because a first-crossing word cannot properly extend another.
It may be empty for small \(E\). Every word in it has slope at most \(\beta\).

**Lemma (stopped exponential moments).** The stopping time is almost surely
finite, and \(\mathbb E e^{sR}<\infty\) for some \(s>0\). The vector
\((Y,R)\) has an exponential moment in a neighborhood of zero.

*Proof.* Put \(X=K-\lambda\). Its mean is \(2-\lambda>0\). Its MGF is
finite around zero, so for some \(t>0\), \(q=\mathbb E e^{-tX}<1\).
If \(\tau>n\), the displacement at depth \(n\) is below three. Markov's
inequality gives

\[
 \Pr(\tau>n)\le e^{3t}q^n.                             \tag{S.tautail}
\]

For small \(s>0\), let \(g(s)=\mathbb E e^{2s(K+1)}\); choose \(s\)
with \(g(s)q<1\). On \(\tau=n\), \(R=\sum_{i\le n}(K_i+1)\). By
Cauchy--Schwarz and \(\Pr(\tau=n)\le\Pr(\tau>n-1)\),

\[
 \mathbb E(e^{sR};\tau=n)
       \le g(s)^{n/2}e^{3t/2}q^{(n-1)/2}.
\]

Summing the geometric majorant proves the claim. Since
\(|Y|\le(1+\lambda)R\), a sufficiently small joint exponential moment
follows. \(\square\)

**Lemma (exact stopped means and concentration).** Set
\(\mu_Y=\mathbb EY\) and \(\mu_R=\mathbb ER\). Then

\[
 \mu_Y=(2-\lambda)\mathbb E\tau\ge3,\quad
 \mu_R=3\mathbb E\tau,\quad
 \frac{\mu_R}{(\log2)\mu_Y}=\frac3{\log(4/3)}.          \tag{S.means}
\]

For each fixed \(\delta>0\) there are finite positive \(C_\delta,c_\delta\)
such that independent stopped copies obey

\[
 \Pr\left(\left|\sum_{i=1}^lY_i-l\mu_Y\right|>\delta l
       \ \text{or}\
       \left|\sum_{i=1}^lR_i-l\mu_R\right|>\delta l\right)
       \le C_\delta e^{-c_\delta l}.                  \tag{S.corridor}
\]

*Proof.* The event \(\tau\ge i\) depends only on \(K_1,\ldots,K_{i-1}\).
Independence and absolute integrability allow summing
\(\mathbb E[K_i1_{\tau\ge i}]=2\Pr(\tau\ge i)\). Thus
\(\mathbb E\sum_{i\le\tau}K_i=2\mathbb E\tau\), which gives the two means
without an unbounded optional-stopping assertion. The stopped displacement
is at least three pointwise. The ratio follows from
\((2-\lambda)\log2=\log(4/3)\). For a centered coordinate
\(Z=Y-\mu_Y\) or \(R-\mu_R\), its log-MGF is differentiable at zero with
derivative zero. Choose \(t>0\) small enough that
\(\log\mathbb Ee^{tZ}<t\delta/2\), and likewise for \(-Z\). Markov's
inequality bounds each of the four tails by \(e^{-t\delta l/2}\); take
the minimum exponent and sum the four bounds. \(\square\)

These constants are effective: (S.tautail) and the displayed geometric
majorant give explicit tails for stopped-word expectations and MGFs.
At fixed depth, a large-valuation tail is bounded by the geometric MGF;
the depth tail is bounded by the majorant above. Finite rational searches
for strict inequalities therefore terminate. Their numerical optimization
is not used in the density score.

### An elementary precision tail with a fully fixed range

**Lemma (two-binomial-tail certificate).** For every integer \(E\ge256\),

\[
 \varepsilon(E)\le2e^{-E/75}\le2^{-E/100}.              \tag{S.timeout}
\]

*Proof.* Put \(N=\lfloor2E/5\rfloor\) and
\(L=\lceil\lambda N+3\rceil\). If
\(L\le\sum_{i\le N}K_i<E\), then the displacement has crossed three by
depth \(N\) and the first-crossing total is below \(E\). Consequently

\[
 \varepsilon(E)\le
 \Pr\{\operatorname{Bin}(L-1,1/2)\ge N\}
 +\Pr\{\operatorname{Bin}(E-1,1/2)\le N-1\}.           \tag{S.binomial}
\]

This is the exact waiting-time correspondence: the sum of \(N\) positive
geometric variables is the trial of the \(N\)-th success. Both \(E-1\)
and \(N-1\) in the second event are essential.

For a sum of \(n\ge1\) fair bits, either centered tail at distance \(a\ge0\)
is at most \(e^{-2a^2/n}\). Indeed a centered bit has MGF
\(\cosh(t/2)\le e^{t^2/8}\), since the derivative of \(\log\cosh u\)
is \(\tanh u\le u\) for \(u\ge0\); symmetry handles \(-t\).
Independence and optimization at \(t=4a/n\) prove the bound.

Use \(\lambda<8/5\), proved by \(3^5<2^8\). With \(n=L-1\),

\[
 n<\tfrac85N+3\le\tfrac{16}{25}E+3\le\tfrac23E,\qquad
 N-\tfrac n2>\tfrac15N-\tfrac32
       \ge\tfrac2{25}E-\tfrac{17}{10}\ge\tfrac1{15}E.
\]

The last inequalities hold for \(E\ge256\). The first probability in
(S.binomial) is therefore at most \(e^{-E/75}\). In the second event
the downward distance is
\((E-1)/2-(N-1)\ge E/10+1/2\), so its probability is at most \(e^{-E/50}\).
Their sum is at most \(2e^{-E/75}\). Finally \(\log2<7/10\): the first
four terms of \(e^{7/10}\) sum to more than two. Thus
\(E(1/75-(\log2)/100)\ge256(19/3000)>\log2\), proving the second bound.
\(\square\)

This conservative exponent fixes an effective continuation schedule. It
does not replace the sharper reference survival certificate used for the
initial word family. In the next section we show that changing to this
continuation after a sufficiently long initial history loses arbitrarily
little marked mass, with that initial choice fixed before the cutoff limit.

### Global indices, finite parsing, and bounded offsets

Fix once and for all

\[
 E_i=\lceil1000\log_2(i+2)\rceil\quad(i\ge1).           \tag{S.precision}
\]

Then \(E_i\ge256\) and (S.timeout) gives
\(\varepsilon(E_i)\le(i+2)^{-10}\). For any word of depth \(d\),
(W.offset) and \(K_i\ge1\) give

\[
 0\le C_w\le\sum_{i=1}^d3^{i-1}2^{-i}
       =(3/2)^d-1.                                   \tag{S.offset}
\]

For concatenated words \(w_i\in V(E_i)\), successive slopes are at most
\(\beta\). The composition identity (W.compose) bounds the complete
offset by the fixed finite number

\[
 C_\infty=\sum_{i\ge1}\beta^{i-1}
                    ((3/2)^{E_i-1}-1)<\infty.         \tag{S.offsetsum}
\]

The bracket grows at most polynomially in \(i\), while \(\beta^{i-1}\)
is geometric. A ratio bound on a polynomial-geometric tail gives effective
truncation. The factors \(\beta^{i-1}\) provide the accumulated contraction in this
sum.

Concatenations of a prescribed finite number of prefix-free blocks have a
unique parsing. Parse the first word at its first crossing, remove it, and
repeat with the next prescribed precision. If one concatenation properly
extended another with the same number of component blocks, this parsing
would force every component to agree and leave no extension. Thus the
concatenation family is prefix-free, as is every restriction of it.

### Rational corridors and finite selection

Fix a rational outer tolerance \(\delta>0\). Effective approximation of
(S.means) supplies rational centers satisfying
\[
 |\widetilde\mu_Y-\mu_Y|<\delta/4,\qquad
 |\widetilde\mu_R-\mu_R|<\delta/4.                    \tag{S.centers}
\]
For a concatenation of \(l\) stopped blocks retain the rational inner bounds
\[
 |Y-\widetilde\mu_Yl|\le(\delta/2)l,\qquad
 |R-\widetilde\mu_Rl|\le(\delta/2)l.                  \tag{S.innercorridor}
\]
The true \(\delta/4\)-corridor is contained in this inner corridor,
which is contained in the true \(\delta\)-corridor. Both inclusions
follow from the triangle inequality. Thus selection preserves the outer
geometric bounds while its rejected mass is controlled by (S.corridor)
at tolerance \(\delta/4\).

This is a decidable finite selection. The \(R\)-comparison is rational.
For a rational endpoint \(a/b\), \(b>0\), comparison of
\(Y=A-d\log_2 3\) with \(a/b\) reduces, when \(bA-a\ge0\),
to comparing the integers \(2^{bA-a}\) and \(3^{bd}\).
If \(bA-a<0\), its sign decides the comparison; depth zero is rational.
Both inequalities defining the absolute-value bound are handled this way.


For the continuation construction, use the effective constants
\(C_{\delta/4},c_{\delta/4}\) from (S.corridor). Every transition
and macroblock below uses these concentration constants, while its
geometric conclusions use the outer tolerance \(\delta\).

### Parent-independent macroblocks at the actual current count

Fix \(\delta=1/20000\) for the later clock, choose the centers above,
and take a fixed \(L>0\) with \(c_{\delta/4} L>10\). For cumulative original-block count \(B\ge0\), define

\[
 \ell(B)=\lceil L\log(B+2)\rceil,\qquad
 B_{j+1}=B_j+\ell(B_j).                               \tag{S.schedule}
\]

A *macroblock* groups \(\ell(B)\) successive stopped blocks. The next
family \(\mathcal C_B\) consists of concatenations
\(w_i\in V(E_i)\), \(B<i\le B+\ell(B)\), satisfying the following
decidable displacement and step-count corridors:

\[
 |\sum Y(w_i)-\widetilde\mu_Y\ell(B)|\le(\delta/2)\ell(B),\qquad
 |\sum R(w_i)-\widetilde\mu_R\ell(B)|\le(\delta/2)\ell(B).
                                                        \tag{S.macro}
\]

It is finite, prefix-free, and independent of the physical parent. Its
reference mass \(p_B\) obeys

\[
 1-p_B\le\ell(B)(B+3)^{-10}
                  +C_{\delta/4} e^{-c_{\delta/4}\ell(B)}
       =O((B+2)^{-9}),\qquad
 h_B\le\sum_{i=B+1}^{B+\ell(B)}(E_i-1)
       =O(\log^2(B+2)).                               \tag{S.macrodeficit}
\]

*Proof.* Independently sample complete stopped blocks. They have total mass
one by (S.tautail); restarting after a finite stopping word gives the same
law because each concatenation has probability equal to the product of its
word probabilities. Reject if any block exceeds its prescribed precision
or either inner corridor fails. By (S.centers)–(S.innercorridor),
that failure implies failure of the true quarter-tolerance corridor.
The union bound, (S.timeout), and (S.corridor) give the estimate. The depth bound follows from \(d\le A<E_i\) for every
component. Since \(\ell(B)=O(\log(B+2))\) and \(c_{\delta/4} L>10\), the
final polynomial bound has constants independent of the starting count
\(B_0\). \(\square\)

In particular \(p_B>0\) eventually. At a fixed starting \(B_0\), every
retained continuation satisfies the summed corridors, with only its fixed
incoming prefix contributing additive constants. The map from displacement
and step count to valuation and depth is invertible:

\[
 d=(R-Y)/(1+\lambda),\qquad
 A=(\lambda R+Y)/(1+\lambda).                         \tag{S.tags}
\]

Windows of width \(O(B)\) in both \(Y,R\) therefore permit \(O((B+1)^2)\)
total integer tags, with constants depending only on the fixed corridors.
Applying (T.capacity) retains this tag cost, the offset envelope, and the
boundary term \(3^q\beta^B\). At \(k=\lceil B/1000\rceil\) and
\(q=k_{\rm next}+h_B\), \(q/B\) tends to
\(1/1000<\log_3 8\), so that boundary term decays exponentially.
For the full history from block one, if \(\epsilon_k\le C_6/k^6\),
(T.pairing) has summable increments: the unrestricted
\(O(B^2\log^2 B)\) tag bound times \(O(B^{-6}+B^{-9})\) is summable even
over every integer \(B\). The tighter corridor tag count removes the
harmless \(\log^2 B\) factor when its literal hypotheses are available.

For the literal application, set
\(k_{\rm old}=\lceil B/1000\rceil\),
\(k_{\rm new}=\lceil(B+\ell(B))/1000\rceil\), and
\(q=k_{\rm new}+h_B\). In (T.stopped), use
\(k=k_{\rm new}\) and its \(\ell=k_{\rm old}\). The hypotheses
\(1\le k_{\rm old}\le q\) hold for \(B\ge1\). Any initial
\(B=0\) stage is separate finite bookkeeping; positive-level mixing is
used only for the eventual tail above.

When the continuation starts after a large count \(B_0\), the schedules (S.precision)
and (S.schedule) use that actual count. Restarting a fixed small macro
index would leave an initial rejection probability without a bound. The next section
also retains the number of incoming tags in the error bound and proves
that its product with the continuation tail tends to zero as the initial
history is extended.


## 4. A finite graft with uniformly vanishing weighted loss {#chapter04}

We need to extend a family with positive marked mass while retaining
control of the trajectories' sizes and step counts. An initial family of
words is called a *seed family*. A *graft* keeps a finite initial segment of
seed blocks, appends a finite transition, and then continues with the
stopped macroblocks of the preceding section. Its *splice index* is the
number of seed blocks retained. The estimate below bounds the marked mass
lost in this change of continuation, uniformly in the root.

Quantitative reference mixing and lower bounds on the seed marks are
explicit premises here. They are established in the mixing, seed-mark and
persistent-root sections. All estimates below retain the actual inverse-history weights
\(\omega=3^d2^{-A}\).

### The seed words and their geometric interface

Fix an integer \(b_0\ge32^5\), and define
\[
 b_{t+1}=b_t+\lfloor b_t/100\rfloor,\quad
 m_b=\lceil b^{3/5}\rceil,\quad
 \gamma=\frac{201}{200},\quad g=\frac{2013}{2000}.
                                                               \tag{G.seed}
\]
Here \(t\) counts seed blocks. At stage \(t\), take exactly the words
\[
 V_t=\{w:|w|=b_t,\quad |A(w)-2b_t|\le m_{b_t}\}.
                                                               \tag{G.fixedseed}
\]
The parameter \(b_t\) also specifies the parent-size threshold \(16^{b_t}\).
Every family is finite, since its positive letters have bounded total
valuation, and prefix-free, since all its words have the same length.
The seed fixes the depth and restricts the total valuation. The later
stopped blocks retain their own first-crossing rule from [Section 3](#chapter03); their
survival and graft estimates are established separately below.

For a positive odd root \(M\ge16^{b_0}\), let \(\mathcal P_t(M)\) contain
the physically realized concatenations of the first \(t\) such words.
The empty concatenation at \(t=0\) is included. Histories retain their
complete words and cuts; identical copies are not counted as different
histories. Write \(x_h,\omega_h,C_h\) for source, slope and offset.
All integral positive odd sources are admitted, including nonunits; markers
at positive level vanish on the latter.

**Lemma (seed geometry and actual capacity).** Set

\[
 C_{\rm tag}=20(4b_0+1),\quad
 C_{\rm in}=C_{\rm tag}(2^{b_0+1}+16^{b_0}),\quad
 P_t=C_{\rm in}(t+1)^3g^t .                           \tag{G.capacityconstant}
\]

Every history in \(\mathcal P_t(M)\) satisfies

\[
 x_h\ge16^{b_t},\quad
 \omega_h\le16^{b_0-b_t},\quad
 0\le C_h\le2^{b_0+1},\quad
 b_0\gamma^t\le b_t\le b_0(101/100)^t.                \tag{G.prefix}
\]

There are at most \(C_{\rm tag}(t+1)^3g^t\le P_t\) total
depth/valuation tags. For
\(H^{\rm in}_{t,q}(a)=\sum_{h:x_h\equiv a\ (3^q)}\omega_h\),

\[
 3^q H^{\rm in}_{t,q}(a)\le P_t\quad(0\le q\le2b_t).
                                                               \tag{G.incapacity}
\]

These bounds are independent of the root and persist under restriction of
the history family without renormalization.

*Proof.* Write \(\lambda=\log_2 3<8/5\), using \(3^5<2^8\).
For \(b\ge32^5\), \(m_b/b\le2b^{-2/5}\le1/512\), so every
selected word satisfies
\[
 Y=A-\lambda b\ge(2-\lambda)b-m_b>b/3,\qquad
 C_w\le(3/2)^b-1<2^b.                               \tag{G.seedgeometry}
\]
The offset estimate is (S.offset). At a parent \(R\ge16^b\), it gives
\(R-C_w>R/2\), and hence
\[
 x=\frac{R-C_w}{\omega_w}>2^{b/3-1}R,\qquad
 \omega_w<2^{-b/3}.
\]
Since \(b/3-1\ge4\lfloor b/100\rfloor\) on the stated range,
\(x\ge16^{\lfloor b/100\rfloor}R\) and
\(\omega_w\le16^{-\lfloor b/100\rfloor}\).
This also gives positivity for every compatible word and its prefixes.
Multiplying proves the endpoint and slope bounds in (G.prefix).

The composition identity (W.compose) bounds the total offset by
\[
 \sum_{j<t}16^{b_0-b_j}2^{b_j}
 \le2^{b_0}\sum_{j\ge0}2^{-3j}<2^{b_0+1},
\]
since \(b_j-b_0\ge j\). Also
\(\lfloor b/100\rfloor\ge b/200\) for \(b\ge200\); the recurrence
bounds in (G.prefix) follow.

For the tag count put \(B_*=\sum_{j<t}b_j\) and
\(m_*=\sum_{j<t}m_{b_j}\). Total depth is exactly \(B_*\), and total
valuation lies in \([2B_*-m_*,2B_*+m_*]\). There are therefore at
most \(2m_*+1\) total depth/valuation tags. The exact comparison
\((101/100)^3<g^5\), together with \(m_b\le2b^{3/5}\), gives
\(m_*\le2t b_0^{3/5}g^t\), whence
\[
 2m_*+1\le(4b_0+1)(t+1)g^t
          \le C_{\rm tag}(t+1)^3g^t.                \tag{G.seedtags}
\]
We retain the latter conservative constant in the continuation estimates.

A source and the total depth determine the canonical forward word;
the prescribed block lengths determine all seed cuts. There is at most
one history per source in each tag. Apply (T.capacity) with offset width
\(2^{b_0+1}\) and slope bound \(16^{b_0-b_t}\). If \(q\le2b_t\),
its boundary term is at most
\(16^{b_0}(9/16)^{b_t}\le16^{b_0}\), giving (G.incapacity).
Restriction can only remove nonnegative weights. \(\square\)

### Inputs and parameter order for the graft

Assume (T.mix) with \(\epsilon_k\le C_6/k^6\) for \(k\ge1\), where the
nonnegative \(C_6\) is fixed. The density recipe uses the particular source
coefficient to be specified in its mixing section; the present implication
holds for any coefficient satisfying this premise.
For \(t\ge0\) put \(a_t=\lfloor b_t/4\rfloor\ge1\), and define the
incoming mark

\[
 Z_t(M)=\sum_{h\in\mathcal P_t(M)}
             \omega_h\,\rho_{a_t}(x_h\bmod3^{a_t}).    \tag{G.inmark}
\]

The geometric lemma above does not assert that this mark is positive.
The later seed-score argument is to supply a fixed finite nonempty pool
\(\mathcal R\) of distinct positive odd roots, all at least \(16^{b_0}\), and
numbers \(z_M\ge0\) such that, for some fixed \(N\),

\[
 Z_t(M)\ge z_M\quad(t\ge N,\ M\in\mathcal R),\qquad
 0<W\le\sum_{M\in\mathcal R}\frac{z_M}{M}.             \tag{G.marks}
\]

The graft theorem preserves the pool, its persistent lower marks \(z_M\),
and its score \(W\).
When counting sources we additionally require (W.antichain) and finite
paths from the roots to the chosen target.

Fix the stopping section's \(\delta=1/20000\), \(\beta=1/8\), means
\(\mu_Y,\mu_R\), rational centers (S.centers), and concentration
constants \(C_{\delta/4},c_{\delta/4}>0\) at tolerance \(\delta/4\).
Choose one integer \(L\ge1\) with \(c_{\delta/4} L>10\). The global precisions
are \(E_i=\lceil1000\log_2(i+2)\rceil\), and macro lengths are
\(\ell(B)=\lceil L\log(B+2)\rceil\). All these choices precede the splice
index \(t\), and \(t\) will precede any physical counting cutoff.

### The transition and its error bound

At a proposed splice \(t\), write

\[
 E=\lfloor\sqrt{b_t}\rfloor,\quad B_0=\lfloor E/4\rfloor,\quad
 k_0=\lceil B_0/1000\rceil,\quad Q=2b_t.               \tag{G.transition}
\]

Take \(B_0\) words from \(V(E)\), and retain the concatenation only if
its total displacement and step count satisfy
\[
 |Y-\widetilde\mu_YB_0|\le(\delta/2)B_0,\qquad
 |R-\widetilde\mu_RB_0|\le(\delta/2)B_0.
\]
These decidable inner bounds imply the outer \(\delta\)-corridors
about the true means, by (S.centers)–(S.innercorridor).
This fixed transition family is finite, prefix-free and independent of the
physical parent. It has maximum depth at most \(B_0(E-1)\le b_t/4\).
For \(E\ge256\), its reference mass \(p_t\) obeys

\[
 1-p_t\le B_0\,2^{-E/100}
                      +C_{\delta/4} e^{-c_{\delta/4} B_0}.   \tag{G.transitionfailure}
\]

Indeed sample \(B_0\) complete stopped blocks first, of total reference mass
one. The union of their precision failures has probability at most
\(B_0\varepsilon(E)\); (S.timeout) and the quarter-tolerance
concentration bound give the two terms.
Retained words keep their original reference weights.

Apply this same family to each incoming endpoint, keeping its original
weight. Mark the resulting physical endpoint at level \(k_0\), and call
the total \(Z^{\rm hyb}_{t,0}(M)\). Physical realization for every compatible
branch will be established below before using the comparison.
For sufficiently large \(t\), \(k_0\ge1\), \(a_t\le Q\), and the maximum
transition depth plus \(k_0\) is at most \(Q\). Use (T.stopped) with the
possibly enlarged depth bound \(h=Q-k_0\), rather than requiring \(Q\) to
be the minimal possible level. Then (G.incapacity) gives

\[
 |Z^{\rm hyb}_{t,0}(M)-Z_t(M)|
 \le D_t^{\rm tr}:=
 \frac23P_t\left\{\frac{C_6}{k_0^6}+\frac{C_6}{a_t^6}
                   +B_0\,2^{-E/100}
                   +C_{\delta/4} e^{-c_{\delta/4} B_0}\right\}.          \tag{G.transitiondebit}
\]

The bound includes both mixing terms and the rejected reference mass. In particular,
the incoming estimate is used only at its allowed level \(Q=2b_t\).

This error bound tends to zero uniformly in the root. To see the dependence
explicitly, for \(E\ge256\) one has
\[
 E\ge\sqrt{b_t}/2,\quad
 \sqrt{b_t}/16\le B_0\le\sqrt{b_t}/4,\quad
 k_0\ge\sqrt{b_t}/16000,\quad a_t\ge b_t/8.
\]
For fixed \(c>0\), \(e^{-cu}\le r!c^{-r}u^{-r}\), by the \(r\)-th
term of the exponential series. Use \(r=7\) on the precision term,
including its factor \(B_0\), and \(r=6\) on the corridor term.
It follows that \(D_t^{\rm tr}\le C_{\rm tr}P_t b_t^{-3}\) for a
fixed effective \(C_{\rm tr}\). Since \(g<\gamma^3\),
\((t+1)^3(g/\gamma^3)^t\to0\), as required.

### Composed offsets and realization of every retained branch

It is useful to replace the stopped section's infinite offset envelope by
a finite rational upper bound. Let

\[
 \overline C_\infty=
 \sum_{i=1}^{1997}8^{1-i}(i+2)^{1000}
       +\frac43\,8^{-1997}2000^{1000}.                \tag{G.offsetconstant}
\]

Then \(C_\infty\le\overline C_\infty\). In fact
\((3/2)^{E_i-1}-1<(i+2)^{1000}\). For
\(D_i=8^{1-i}(i+2)^{1000}\) and \(i\ge1998\), the binomial theorem gives
\[
 \frac{D_{i+1}}{D_i}
 =\frac18\left(1+\frac1{i+2}\right)^{1000}
 \le\frac1{8(1-1000/(i+2))}\le\frac14.
\]
Summing this geometric tail proves the assertion.

The transition counts as the first \(B_0\) appended stopped blocks. Its
exceptional common precision \(E\) is not substituted into the later
logarithmic schedule. At every later macro start use its actual cumulative
appended count:

\[
 B_{j+1}=B_j+\ell(B_j),\qquad
 \mathcal C_{B_j}\text{ uses the indices }B_j<i\le B_{j+1}.
                                                               \tag{G.continuation}
\]

Every complete appended word, through any such stage, has slope at most
\(\beta^B\) and offset at most
\[
 C_{\rm app}\le
       \frac{(3/2)^{E-1}}{1-\beta}+\overline C_\infty .
\]
For the transition this is a geometric sum over its \(B_0\) contractions.
For the later blocks the preceding contractions are \(\beta^{i-1}\),
including the transition, so their contribution is a tail of the global
envelope. The continuation therefore uses its actual cumulative block index.

Compose with an incoming seed history:
\[
 M=\omega_{\rm pre}\omega_{\rm app}x+
                  C_{\rm pre}+\omega_{\rm pre}C_{\rm app}.
\]
By (G.prefix), \(E\le b_t\), and \(3/2<2\),

\[
 \omega_{\rm pre}C_{\rm app}
 \le16^{b_0}\left\{\frac87\,2^{-3b_t}
                  +\overline C_\infty\,2^{-4b_t}\right\}
       \longrightarrow0.                             \tag{G.offsetabsorption}
\]

Choose a fixed splice threshold so that the displayed bound is at most one
thereafter, and put \(C_*:=2^{b_0+1}+1\). Every total offset is then at most
\(C_*<16^{b_0}\le M\), uniformly in root, stage and level.
The same bound holds for prefixes of a selected appended word, whose offset
partial sums only increase. By (T.injection), compatibility gives integrality
of every endpoint; the strict offset margin and (W.inverse) give positivity
and oddness. Thus each formal compatible branch counted by the transfer is
exactly a physical branch with the stated valuations. These are precisely the branches used in the transition and continuation
comparisons.

### Uniform continuation capacity and its complete tail

The transition corridor and all subsequent macro corridors add. At a
cumulative count \(B\ge B_0\), every retained appended word satisfies
\[
 |Y_{\rm app}-\mu_YB|\le\delta B,\qquad
 |R_{\rm app}-\mu_RB|\le\delta B.                      \tag{G.totalcorridor}
\]
Under (S.tags), the possible depths occupy an interval of length
\(4\delta B/(1+\lambda)\), and the valuations an interval of length
\(2\delta B\). Since \(\lambda>1\) and \(2\delta<1\), there are at most
\((B+1)^2\) appended integer tags. Together with the incoming tag count
this permits at most \(P_t(B+1)^2\) combined total tags.

Within a combined total tag, a source determines its complete forward word.
Its reversal determines the first \(t\) seed cuts, then the \(B_0\)
transition first crossings and all later prescribed macro cuts. Hence there
is at most one history per source in a tag, even if multiple pairs of
incoming/appended tags have the same sum. Applying (T.capacity) anew, with
the composed offset width and \(\omega_{\rm pre}\le1\), gives

\[
 3^qH^{\rm hyb}_{t,B,q}(a)
       \le P_t(B+1)^2(C_*+3^q\beta^B)
                           \qquad(q\ge0).             \tag{G.hybridcapacity}
\]

Unlike (G.incapacity), this fresh spacing estimate is valid at every
level. All its constants were fixed before \(t\).

For definiteness, the following explicit threshold suffices to control the
boundary term:

\[
 B_{\rm cap}=[400000(L+1)]^2,\quad
 D_{\rm mac}=L+1+C_{\delta/4},\quad
 K_{\rm var}=\frac83(C_*+1)(2C_6\,1000^6+D_{\rm mac}). \tag{G.tailconstants}
\]

At a macro start \(B\), put \(B'=B+\ell(B)\),
\(k=\lceil B/1000\rceil\), \(k'=\lceil B'/1000\rceil\), and
\[
 h_B=\sum_{i=B+1}^{B'}(E_i-1),\qquad q(B)=k'+h_B.
\]
For every \(B\ge B_{\rm cap}\), \(q(B)\le B/2\), and therefore
\(3^{q(B)}\beta^B\le1\). Here is a direct bound with no hidden dependence
on the splice. Write \(a=L+1\). For \(B\ge2\),
\(\ell(B)\le a\log(B+2)\). The inequality
\(\log x\le4x^{1/4}\) for \(x\ge1\) shows
\(\ell(B)\le5a B^{1/4}\le B\) at the stated threshold.
For the corresponding indices, \(i+2\le2(B+2)\). Since
\(\log2>1/2\), one obtains
\[
 h_B\le4000a\log^2(B+2),\qquad
 q(B)\le B/1000+4002a\log^2(B+2).
\]
Also \(\log^2(B+2)\le16\sqrt{B+2}\le24\sqrt B\). Using
\(\sqrt B\ge400000a\), the last bound is at most
\[
 \left(\frac1{1000}+\frac{96048}{400000}\right)B
       =\frac{96448}{400000}B<B/2.
\]
The logarithmic inequalities follow from the exponential series and
\(\log2=\int_1^2x^{-1}\,dx>1/2\); no numerical fit is used.

The macro failure estimate (S.macrodeficit) satisfies the explicit bound
\[
 1-p_B\le \frac{D_{\rm mac}}{(B+2)^9}.
\]
Indeed \(\ell(B)\le(L+1)(B+2)\), and
\(e^{-c_{\delta/4}\ell(B)}\le(B+2)^{-c_{\delta/4} L}\le(B+2)^{-10}\).
Both marker errors are at most \(C_6(1000/B)^6\). Pair (T.stopped) at
\(k',k,q(B)\) with (G.hybridcapacity); all these are positive marker
levels once \(B\ge B_{\rm cap}\). The marked increments satisfy

\[
 |Z^{\rm hyb}_{t,j+1}(M)-Z^{\rm hyb}_{t,j}(M)|
             \le K_{\rm var}P_t B_j^{-4}.             \tag{G.increment}
\]

This uses \((B+1)^2\le4B^2\), the boundary bound, and the two distinct
mixing costs. The current marker in \(Z^{\rm hyb}_{t,j}\) is always
\(\rho_{\lceil B_j/1000\rceil}\).

The visited \(B_j\)'s are increasing integers. For \(B_0\ge2\),
\[
 \sum_{n\ge B_0}n^{-4}
 \le\int_{B_0-1}^\infty x^{-4}\,dx
 =\frac1{3(B_0-1)^3}\le3B_0^{-3}.
\]
Consequently the total continuation error bound, including its first macro, is
at most \(3K_{\rm var}P_tB_0^{-3}\). The bound is uniform in the splice.

### The graft theorem and the fixed-root quantifiers

**Theorem (finite graft).** At all sufficiently late splices \(t\), the
construction above is physically realized and, for every \(j\ge0\) and
every positive odd root \(M\ge16^{b_0}\),

\[
 |Z^{\rm hyb}_{t,j}(M)-Z_t(M)|\le\Delta_t,\qquad
 \Delta_t=D_t^{\rm tr}+3K_{\rm var}P_tB_0^{-3}
                     \longrightarrow0.              \tag{G.graft}
\]

Each hybrid marked sequence has a nonnegative limit, with the same bound.
If the fixed pool satisfies (G.marks), then for every \(\eta>0\) there is
one finite common splice \(t\ge N\) such that

\[
 \sum_{M\in\mathcal R}\frac{Z^{\rm hyb}_{t,j}(M)}M
                  \ge W-\eta\qquad(j\ge0).            \tag{G.pool}
\]

The same holds for its limit. Neither the root pool nor \(W\) depends on
\(\eta\), the stage or any subsequent counting cutoff.

*Proof.* Choose \(t\) beyond the offset threshold, with \(E\ge256\) and
\(B_0\ge B_{\rm cap}\). The realization argument validates the finite
transition comparison and every continuation comparison. Sum
(G.increment) and (G.transitiondebit) to obtain (G.graft).
Absolute summability gives the limit and preserves nonnegativity.

The transition error bound has already been shown to tend to zero. For the other
term, (G.prefix) and \(B_0\ge\sqrt{b_t}/16\) imply
\[
 P_tB_0^{-3}
 \le4096C_{\rm in}b_0^{-3/2}(t+1)^3
                         (g/\gamma^{3/2})^t\longrightarrow0,
\]
because
\[
 \gamma^3-g^2=\frac{16263}{8000000}>0 .
\]
All thresholds and constants are independent of the root and of the chosen
later splice; they are effective from the displayed rules and the effective
stopped-law constants.

Finally fix the pool and let \(S=\sum_{M\in\mathcal R}1/M>0\).
Choose a single \(t\ge N\) with \(\Delta_tS<\eta\).
Use \(Z_t(M)\ge z_M\) and sum (G.graft) with the positive coefficients
\(1/M\). This proves (G.pool) for the pooled marks. If \(\eta<W\), at least one retained family is nonempty at every
stage. The choice of \(t\) is made before a physical cutoff is introduced.
\(\square\)

### State supplied to the terminal construction

For the convergence-to-one specialization, suppose the fixed pool is
a convergent antichain satisfying (W.antichain), with specified finite
root-to-one paths. This includes (R.pool). For the fixed pool and splice, let
\[
 A_t^{\max}=\sum_{r<t}(2b_r+m_{b_r}),\qquad
 T_t^{\max}=\sum_{r<t}(3b_r+m_{b_r}).
\]
The fixed depths and valuation windows give these upper bounds on incoming valuation
and ordinary step count. In particular \(\omega_{\rm pre}\ge2^{-A_t^{\max}}\).
Let \(M_-=\min\mathcal R\), \(M_+=\max\mathcal R\), and
\(T_{\mathcal R}=\max_{M\in\mathcal R}\tau_1(M)\), finite by the specified
paths. Immediate predecessors of one are a special case.
For every retained source at a central count \(B=B_j\),

\[
 \begin{split}
 (\mu_Y-\delta)B+\log_2(M_--C_*)
     &\le\log_2x
       \le(\mu_Y+\delta)B+\log_2M_++A_t^{\max},\\
 \tau_1(x)&\le(\mu_R+\delta)B+T_t^{\max}+T_{\mathcal R}.
 \end{split}                                         \tag{G.terminalstate}
\]

Indeed \(x=(M-C_{\rm total})2^{Y_{\rm app}}/\omega_{\rm pre}\);
use \(0\le C_{\rm total}\le C_*<M_-\), the two slope bounds, and
(G.totalcorridor). The ordinary step count is the actual sum \(A+d\), and
adding the root-to-one path gives the second line. These inequalities are
uniform over the whole fixed finite pool, even if some root families are
empty.

The terminal construction will use these bounds to obtain sources in a
common interval at every sufficiently large scale. It must retain the
same histories, weights and one fixed splice throughout.

### Connection to the terminal construction

The seed used here is the fixed-depth family (G.fixedseed). The estimates above
control the transition and continuation errors uniformly in the root.
Reference mixing and the persistent seed-mark premise (G.marks) are the two
remaining inputs to this construction; the later sections prove them with
the choices needed here. The next step is to place the resulting sources
in short intervals at every sufficiently large scale.

## 5. Terminal sources at every sufficiently large scale {#chapter05}

The preceding graft preserves a fixed pool's marked mass while controlling
the displacement and ordinary step count of its histories. Here we place the
outer sources in a short multiplicative interval at every large scale,
compress their terminal overshoot, and count each physical source once.
This is the interface used by all the later density bounds.

The shifted first-crossing barrier follows [3, §3]; terminal scale
selection, even overshoot compression and the reference fan follow
[3, §5]. We prove the probability and integer-trajectory estimates needed
here, including the ordinary clock for the compressed sources.

### Graft and terminal parameter lookup {#terminal_notation}

The numerical construction below uses \(\theta=1/1000\).
The parameterized source theorem allows every fixed \(0<\theta\le1/1000\);
the table records both choices.

| Quantities | Role and order of choice | Definition |
|---|---|---|
| \(\mathcal R,W\) | Fixed roots and persistent score, chosen before the clock; counting also uses nonrecurrence | (G.marks), (W.antichain) |
| \(y_\star,T_{\mathcal R}\) | Fixed target and finite maximum root-to-target path length; \(y_\star=1\) in the convergence construction | (G.terminalstate), (N.targetfamily) |
| \(\theta,\delta=\theta/20\) | Terminal ratio and concentration tolerance; positive and fixed before the splice | (N.everyclock), (N.parammargin) |
| \(L,\ell(B),E_i\) | Macro-block length \(\ell(B)=\lceil L\log(B+2)\rceil\) and global word precisions; \(L\) depends on \(\delta\) | (S.schedule), (S.precision) |
| \(t,B_0,B\) | Seed splice index, initial appended block count, and current appended block count | (G.transition), (G.terminalstate) |
| \(\mu_Y,\mu_R\) | Mean binary displacement and ordinary step cost per stopped block | (S.means) |
| \(\widetilde\mu_Y,\widetilde\mu_R\) | Rational centers for the inner corridor; concentration is used at tolerance \(\delta/4\) | (S.centers), (S.innercorridor) |
| \(b=\lfloor\theta B\rfloor,\ k=\lceil\theta B\rceil\) | Terminal size and reference level, growing with the stage | (N.stage), (N.everyclock) |
| \(w_b,l_b,h_b,e_b,r_b\) | Crossing window, overshoot scale and range of terminal shifts | (N.parameters) |
| \(u,K=e_b\) | Parent-dependent barrier shift and retained overshoot cap | (N.words), (N.stage) |
| \(I_B,R_X\) | Common interval of counting cutoffs and actual source-shell radius | (N.common), (N.everyclock) |

Here \(B\) counts stopped reference blocks; it is not the number of
valuation letters. The seed sizes \(b_j\) and the terminal size \(b\)
are distinct. After the clock and tolerance are fixed, the splice and
its schedules stay fixed while \(B,b,k\) grow with the counting cutoff.

### A finite terminal family and its exact reference deficit

Let \(\lambda=\log_2 3\) and \(J(v)=\lceil\lambda v\rceil\) for
nonnegative integers \(v\), with \(J(0)=0\). For an integer \(b\ge200\), put

\[
 w_b=\lfloor3b/5\rfloor,\quad l_b=b-w_b,\quad h_b=b+w_b,
 \quad e_b=\lfloor b/100\rfloor,\quad
 r_b=2w_b-J(w_b)-2e_b.                               \tag{N.parameters}
\]

The integer \(r_b\) is nonnegative. More precisely,

\[
 \frac{229}{1000}b-2\le r_b
       \le\frac35(2-\lambda)b,\qquad e_b\ge b/200.    \tag{N.radius}
\]

Indeed \(\lambda<317/200\), as \(3^{200}<2^{317}\). Using
\(w_b\ge3b/5-1\), \(J(w_b)\le\lambda w_b+1\), and
\(e_b\le b/100\) gives the lower bound with additive loss less than two.
The upper bound follows from \(J(w_b)\ge\lambda w_b\) and \(e_b\ge0\).
The last floor inequality holds for every \(b\ge200\).

For an integer \(0\le u\le2r_b\), define the nondecreasing integer barrier

\[
 H_{b,u}(s)=2b+J((s-b)_+)-J((b-s)_+)+u-r_b.           \tag{N.barrier}
\]

For an inverse word \(v=(k_1,\ldots,k_d)\), write \(A_s=\sum_{i\le s}k_i\).
For an integer cap \(K\ge0\), let \(\mathcal V(b,u,K)\) consist of words
satisfying

\[
 l_b<d\le h_b,\quad A_s<H_{b,u}(s)\ (l_b\le s<d),
 \quad 0\le A_d-H_{b,u}(d)\le K.                    \tag{N.words}
\]

The miss at \(l_b\) is required; the first crossing is the first one after
that depth, not necessarily the first one from depth zero. This family is
finite, since depth and total valuation are bounded, and prefix-free: a
proper extension of a selected word already has its eligible crossing.
Its unnormalized reference mass is
\(p(b,u,K)=\sum_{v\in\mathcal V(b,u,K)}2^{-A_d}\).

**Lemma (two endpoint tails and overshoot).** Uniformly over the indicated
integers \(b,u,K\),

\[
 1-p(b,u,K)\le2e^{-b/64000}+2^{-(K+1)}.              \tag{N.deficit}
\]

*Proof.* In the geometric reference law, put \(S_s=A_s-2s\).
The exact endpoint identities are

\[
 H_{b,u}(l_b)-2l_b=2e_b+u,\qquad
 H_{b,u}(h_b)-2h_b=u-2r_b-2e_b.                     \tag{N.endpoints}
\]

If the lower-endpoint miss or subsequent crossing by \(h_b\) fails, then
\[
 S_{l_b}\ge2e_b\quad\hbox{or}\quad S_{h_b}<-2e_b.
\]
For the second implication, a miss at \(l_b\) with no eligible hit leaves
\(A_{h_b}<H_{b,u}(h_b)\le2h_b-2e_b\). This is an event on the incoming state and its reference continuation.

The exact waiting-time correspondence used in (S.binomial) gives

\[
 \begin{split}
 \Pr(S_{l_b}\ge2e_b)
 &=\Pr\{\operatorname{Bin}(2l_b+2e_b-1,1/2)\le l_b-1\},\\
 \Pr(S_{h_b}<-2e_b)
 &=\Pr\{\operatorname{Bin}(2h_b-2e_b-1,1/2)\ge h_b\}.
 \end{split}                                         \tag{N.coin}
\]

The respective distances from the binomial means are both \(e_b+1/2\).
Both numbers of trials are positive, and at most \(16b/5\): for the first,
\(2l_b+2e_b-1\le(41/50)b+1\le b\); for the second use \(h_b\le8b/5\).
The fair-coin Chernoff bound proved in the stopping section and
\(e_b\ge b/200\) therefore bound each probability by
\[
 \exp\left(-\frac{2(e_b+1/2)^2}{16b/5}\right)
 \le e^{-b/64000}.
\]

For an eligible first-hit prefix ending at depth \(d-1\), let
\(a=H_{b,u}(d)-A_{d-1}\). The preceding miss and monotonicity of the
barrier imply \(a\ge1\). Conditional on the next valuation being at least
\(a\), the probability that it exceeds \(a+K\) is exactly
\(2^{-(K+1)}\). Sum over disjoint first-hit events. The overshoot failure
has mass \(2^{-(K+1)}\) times the uncapped crossing mass, hence at most
\(2^{-(K+1)}\). This proves (N.deficit). \(\square\)

### Physical realization, compression, and a sharp shell

For a terminal parent \(y\ge16^b\), every residue-compatible word in
\(\mathcal V(b,u,K)\) is physically realized. In fact (S.offset) gives

\[
 0\le C_v\le(3/2)^d-1<2^b,\qquad
 C_v/y<\eta_b:=8^{-b}.                              \tag{N.offset}
\]

Here \(d\le8b/5\) and \((3/2)^8<2^5\). Compatibility gives integrality
of every prefix by (T.injection); the strict offset margin gives positivity,
oddness and the exact valuations by (W.inverse). This applies to all caps,
not only to the compressed family. If the parent is a multiple of three,
no nonempty inverse word is compatible; its positive-level marker is
also zero.

The terminal *overshoot* is the excess of the total valuation over its
crossing barrier. The next lemma reduces an arbitrary retained overshoot
to zero or one by removing an even number from the last valuation. The resulting source relation leads
to an affine family, called the *fan*.

For \(j\ge0\) put

\[
 F_j(x)=4^jx+\frac{4^j-1}{3},\qquad
 H_k(x)=\sum_{j\ge0}4^{-j}\rho_k(F_j(x)).              \tag{N.fan}
\]

The second series is convergent, since \(\rho_k\) is a bounded function
on a finite residue group. All its arguments are reduced modulo \(3^k\).
Thus \(H_k(x)\) combines all the reference factors in the fan, with their
relative weights. Keeping the index of a fan member will preserve the
identity of the original history during compression.

**Lemma (even overshoot compression).** A physical word with overshoot
\(O\le K\) has a unique image consisting of a word with overshoot at most
one and the integer \(j=\lfloor O/2\rfloor\). Its parent, earlier inverse endpoints, shift
and depth are unchanged. If \(x\) and \(v\) are the reduced source and
complete physical weight, the original source and weight are

\[
 x_{\rm old}=F_j(x),\qquad v_{\rm old}=4^{-j}v.        \tag{N.compress}
\]

*Proof.* Subtract \(2j\) from the last valuation. If the preceding total
is \(A_{d-1}\), the old last valuation is
\(H_{b,u}(d)-A_{d-1}+O\), whose first term is at least one. The new
valuation is positive and its overshoot is zero or one. Earlier misses
and the first-crossing depth are unchanged. Removing an even number preserves
last-step admissibility modulo three. The reduced word has the same offset
bound (N.offset), so every inverse endpoint remains positive and odd.

At the common penultimate endpoint, the identity
\(3F_j(x)+1=4^j(3x+1)\) gives the source formula. The total valuation has
fallen by \(2j\), giving the weight formula. Raising that last valuation
by \(2j\) recovers the original word. Thus the map is injective while
the fan index is retained. \(\square\)

Define

\[
 g_b=2(1-\eta_b),\quad
 L_b(y)=\frac{4^b y}{4\,2^{r_b}3^b},\quad
 L_b^\sharp(y)=g_bL_b(y),\quad
 \mathcal R_b=\frac{16}{1-\eta_b}.                    \tag{N.scales}
\]

**Lemma (source bounds after compression).** Every compatible terminal
source with overshoot at most one
satisfies

\[
 2^uL_b^\sharp(y)\le x
       \le\frac8{1-\eta_b}\,2^uL_b^\sharp(y).         \tag{N.shell}
\]

*Proof.* For \(d=b+v\), the rounding error
\(J(v)-\lambda v\) belongs to \([0,1)\); for \(d=b-v\), its negative
belongs to \((-1,0]\). Consequently, with overshoot at most one,
\[
 \tfrac12(4/3)^b2^{u-r_b}
       \le2^{A_d}3^{-d}\le4(4/3)^b2^{u-r_b}.
\]
Use \(x=(y-C_v)2^{A_d}3^{-d}\), (N.offset), and the definition of
\(L_b^\sharp\). \(\square\)

For every
\(L_b^\sharp(y)<X\le2^{2r_b}L_b^\sharp(y)\), choose the least integer
\(u=u(y,X)\) with \(2^uL_b^\sharp(y)\ge X\). Then

\[
 1\le u\le2r_b,\quad
 X\le2^uL_b^\sharp(y)<2X,\quad
 X\le x<\mathcal R_bX.                              \tag{N.selector}
\]

The strict lower endpoint explains why the chosen shift is at least one;
the reference estimates also include the unused boundary shift zero.
The ratio \(\mathcal R_b\) tends to 16. The offset estimate (N.offset) gives the stated finite-radius correction.

### One common interval for the fixed pool

Assume (T.mix) with \(\epsilon_k\le C_6/k^6\), and the admissible pool
and persistent marks (G.marks), with the convergent antichain specified
at (G.terminalstate). Fix a sufficiently late graft as in
(G.graft). Its current appended counts are \(B=B_j\), with
\(B_{j+1}=B_j+\ell(B_j)\). Write

\[
 b=\lfloor B/1000\rfloor,\quad k=\lceil B/1000\rceil,
 \quad K=e_b,\quad \delta=1/20000.                  \tag{N.stage}
\]

From (G.terminalstate), there are fixed constants \(c_-,c_+,c_\tau\),
uniform over the whole finite pool, such that every current endpoint \(y\)
satisfies

\[
 (\mu_Y-\delta)B+c_-\le\log_2y\le(\mu_Y+\delta)B+c_+,
 \quad \tau_1(y)\le(\mu_R+\delta)B+c_\tau.            \tag{N.central}
\]

These constants include the chosen finite seed/graft and the root-to-one
paths. They do not depend on the terminal cutoff or later stage. Since
\(\mu_Y\ge3\), all these endpoints satisfy \(y\ge16^b\) eventually.
We always work beyond that threshold and \(b\ge200\).

Put
\[
 a(B)=\log_2g_b+(2-\lambda)b-r_b-2,
\]
\[
 A(B)=(\mu_Y+\delta)B+c_++a(B),\qquad
 D(B)=(\mu_Y-\delta)B+c_-+a(B)+2r_b,
 \quad I_B=(2^{A(B)},2^{D(B)}].                      \tag{N.common}
\]

Every \(X\in I_B\) is in the selector interval for every retained
endpoint: its lower endpoint dominates all \(L_b^\sharp(y)\), and its
upper endpoint is below all \(2^{2r_b}L_b^\sharp(y)\). The interval (N.common) uses the fixed deterministic bounds for the whole
pool.

**Lemma (coverage of a half-line).** At all sufficiently late central stages
\(I_B\) is nonempty, consecutive intervals overlap, and their union contains
every sufficiently large real number. A stage chosen for \(X\to\infty\)
necessarily has \(B\to\infty\).

*Proof.* From (N.radius) and \(b\ge B/1000-1\),

\[
 D(B)-A(B)=2r_b-2\delta B+c_--c_+
       \ge\frac{179}{500000}B-C                    \tag{N.room}
\]

for a fixed \(C\). To check consecutive overlap, use the deterministic
endpoints themselves. If \(b'\ge b\), the floor and ceiling formulas give
\(w_{b'}-w_b\le(3/5)(b'-b)+1\),
\(e_{b'}-e_b\le(b'-b)/100+1\), and
\(J(w_{b'})-J(w_b)\le\lambda(w_{b'}-w_b)+1\).
Thus \(|r_{b'}-r_b|\le3(b'-b)+7\). Also
\(|\log_2g_{b'}-\log_2g_b|\le1\).
With \(B'=B+\ell(B)\), we have
\(b'-b\le\ell(B)/1000+1\), so both
\(|A(B')-A(B)|\) and \(|D(B')-D(B)|\) are \(O(\log(B+2))\).
All constants here were fixed with the graft. This logarithmic change is
smaller than the positive linear width in (N.room), proving both inequalities
needed for consecutive intersection.

Finally (N.radius) gives
\(a(B)\ge\log_2g_b+(2/5)(2-\lambda)b-2\), which tends to infinity.
Both interval ends therefore tend to infinity. Their consecutive intersections
make the tail union an interval unbounded above, hence it contains a half-line.
Any fixed finite collection of the \(I_B\)'s is bounded. Thus selecting an
interval containing an increasingly large \(X\) forces its stage to increase.
 \(\square\)

### Controlling the parent-dependent terminal choice

For each \(X\in I_B\), append \(\mathcal V(b,u(y,X),K)\) to each
current endpoint \(y\), retaining the complete history. Let
\(Z^{\rm ter}_{B,X}(M)\) be its physical mass at root \(M\), marked by
\(\rho_k\) at the original, uncompressed outer source. Write
\(Z^{\rm hyb}_{B}(M)\) for the current graft mark.

The terminal family depends on \(y\), so a single common-family transfer
cannot be applied to all parents at once. Partition them by their selected
integer shift. There are at most \(2r_b+1\le2b+1\le B\) groups at the
stages under consideration. Each restricted histogram inherits
(G.hybridcapacity) without renormalization.

Use the ambient level \(q=h_b+k\), child marker \(k\), and old marker
\(k\) in (T.stopped). At \(B\ge200000\),
\[
 q\le\tfrac{13}{5}b+1\le\tfrac{13}{5000}B+1\le B/2,
 \qquad 3^q\beta^B\le1.
\]
The all-level graft capacity is therefore applicable, and every compatible
terminal branch is physical by (N.offset). Sum the comparisons only after
restricting to the actual shift groups. It follows that

\[
 \sup_{X\in I_B}|Z^{\rm ter}_{B,X}(M)-Z^{\rm hyb}_{B}(M)|
 \le d_B:=\frac23 P_t(B+1)^2(C_*+1)(2r_b+1)
       \left(\frac{2C_6}{k^6}+2e^{-b/64000}+2^{-(e_b+1)}\right)
 \longrightarrow0.                                \tag{N.payment}
\]

Here \(P_t,C_*\) are the fixed graft constants. The limit is uniform in \(M\) and \(X\): \(k\ge B/1000\),
\(b\ge B/2000\) eventually, and the right side is
\(O(P_tB^{-3})\) plus polynomial factors times decaying exponentials.
Both marker substitutions, the selected-family deficit, the shift count,
and the level boundary are included in this bound.

### Aggregate source weights and the terminal fan

Replace each terminal family by its physically realized family with
overshoot at most one, retaining
the same central histories, parent-dependent shift, and fixed stage. Count
each complete reduced history just once, not once for each original that
compresses to it. For a reduced history \(z\) from root \(M\), denote its
weight and source by \(v(z)\) and \(x_z\).

At a fixed root \(M\) in the convergent antichain, a source determines its
complete forward orbit and cannot visit \(M\) twice. Reversing its uniquely determined word recovers
the seed cuts, the fixed transition stops, and the prescribed subsequent
stopped-block and macro cuts. The current parent is then determined, its
shift is the selector \(u(y,X)\), and the terminal word is fixed. Thus a
source supports at most one complete reduced history at this stage.

The affine identity gives \(x_zv(z)\le M\). The pool satisfies
(W.antichain), so (W.poolcharge) applies after identifying reduced histories.
After division by the root and grouping by actual source, this gives

\[
 a_x:=\sum_{M\in\mathcal R}\frac1M
             \sum_{z:x_z=x}v(z)\le\frac1x.           \tag{N.charge}
\]

By (N.compress), originals inject into pairs \((z,j)\). First sum only
this finite image, then enlarge to all reduced histories and all \(j\ge0\),
using nonnegativity. The normalized original terminal mark satisfies

\[
 \mathscr A_{B,X}:=\sum_{M\in\mathcal R}
                      \frac{Z^{\rm ter}_{B,X}(M)}M
       \le\sum_x a_xH_k(x).                         \tag{N.fancharge}
\]

The fan index is summed only in the marked inequality. The reduced source
weights in (N.charge) count each history once at the single selected stage.

### Fine precision and the reduced-source clock

For any current endpoint \(y\), the lower end of the common interval gives
\[
 X>L_b^\sharp(y)
   \ge\frac{g_b16^b}{4\,3^b},
\]
because \(r_b\le2b\). Since \(k\le b+1\),

\[
 \frac{3^k}{X}\le\frac{12}{g_b}(9/16)^b
                  \longrightarrow0.                \tag{N.precision}
\]

This includes the genuine ceiling case \(k=b+1\). The limit is uniform
over all cutoffs in the common interval. Also \(k\to\infty\) with the
selected stage.

For every terminal word of cap \(K=e_b\), monotonicity of \(J\),
\(u-r_b\le r_b\), and the exact radius identity imply
\[
 A_d\le2b+J(w_b)+r_b+e_b=2b+2w_b-e_b,
 \quad A_d+d\le3b+3w_b-e_b\le\frac{24}{5}b.
\]
The family with overshoot at most one has the same last bound, since \(e_b\ge2\). Thus the
looser retained coefficient \(481/100\) also bounds its terminal step count.


The reduced source itself is eventually at least its current parent:
from (N.shell), \(u\ge0\), and (N.radius),
\[
 \log_2\frac{x}{y}
 \ge\log_2g_b+(2-\lambda)b-r_b-2
 \ge\log_2g_b+\frac25(2-\lambda)b-2>0.
\]
Combining this size bound with (N.central) gives, uniformly over reduced
sources and cutoffs,
\[
 \limsup \frac{\tau_1(x)}{\log x}
 \le\frac{\mu_R+\delta+481/100000}
             {(\log2)(\mu_Y-\delta)}.               \tag{N.clock}
\]
Here the limit runs through the central stages, and fixed prefix/root step counts
are already included in \(c_\tau\). The denominator is a lower bound on
the logarithm of the reduced source, not that of its larger original.

By (S.means), the right side is decreasing in \(\mu_Y\ge3\). At three it
is
\[
 \frac9{(3-\delta)\log(4/3)}
       +\frac{\delta+481/100000}{(3-\delta)\log2}
 <\frac{1747479290400}{167532267749}
 <\frac{10431}{1000}.                                \tag{N.clockmargin}
\]
For a short exact verification, the positive atanh series
\(\log((1+z)/(1-z))=2\sum_{j\ge0}z^{2j+1}/(2j+1)\) gives
\(\log(4/3)>2(1/7+1/(3\cdot7^3)+1/(5\cdot7^5))\) and
\(\log2>2(1/3+1/(3\cdot3^3)+1/(5\cdot3^5))>693/1000\).
Substituting these lower bounds gives the displayed rational upper bound;
the final cross-multiplied gap is
\[
 10431\cdot167532267749
       -1000\cdot1747479290400=49794489819>0.
\]
The series follows by integrating the geometric series on \([0,z]\).
Because (N.clock) is uniform, increasing the stage threshold for each
fixed finite extension ensures that every later reduced source satisfies the literal
ordinary step bound \(\tau_1(x)\le(10431/1000)\log x\).

### The all-scale physical source-family theorem

**Theorem.** Suppose the mixing and finite-pool premises of (G.marks) hold
with certified score \(W>0\), and the pool is a convergent antichain as
specified at (G.terminalstate). For every \(\varepsilon>0\) and every fixed
\(\Lambda>16\), one can choose one finite common graft and a threshold
\(X_0\) such that, for every real \(X\ge X_0\), there are a finite set of
odd sources \(S_X\), nonnegative weights \(a_x\), a level \(k(X)\),
and a normalized original terminal mark \(\mathscr A_X\) satisfying

\[
 \begin{split}
 S_X&\subseteq[X,\Lambda X)\cap
          \{x:\tau_1(x)\le(10431/1000)\log x\},\qquad a_x\le1/x,\\
 W-\varepsilon&\le\mathscr A_X\le\sum_{x\in S_X}a_xH_{k(X)}(x),\\
 k(X)&\longrightarrow\infty,\qquad 3^{k(X)}/X\longrightarrow0.
 \end{split}                                        \tag{N.sourcefamily}
\]

The fixed pool and \(W\) do not depend on \(\varepsilon,\Lambda,X\).
The graft and its schedules are fixed before \(X\); its selected terminal
stage and shift families may depend on \(X\).

*Proof.* Put \(a=\min\{\varepsilon/2,W/4\}>0\). Use (G.pool) to fix
one common graft with central normalized marks at least \(W-a\) at every
later stage. The reciprocal-root sum \(S=\sum_{M\in\mathcal R}1/M\) is
fixed and finite. By (N.payment), \(Sd_B<a\) eventually, so
\(\mathscr A_{B,X}\ge W-2a\ge W-\varepsilon\) uniformly on \(I_B\).
In particular positive original terminal mass is retained.

Increase this fixed stage threshold until the common intervals cover their
tail, \(\mathcal R_b<\Lambda\), and the reduced-source clock holds.
For every sufficiently large \(X\), select one of these intervals containing
it and take its whole pooled reduced family. Apply (N.selector), (N.charge),
and (N.fancharge). The stage must tend to infinity with \(X\), so
(N.precision) gives both final limits. All limiting assertions are uniform
over the cutoffs in each selected interval. The graft is fixed at the chosen positive error tolerance. \(\square\)

### Clocks arbitrarily close to the stopped-mean ratio

Put \(c_0=3/\log(4/3)\). The fixed numerical construction above
has a parameterized version with the same incoming pool and score.

**Theorem (parameterized source families).** Under the mixing and
persistent-pool hypotheses of (G.marks), with the same convergent
antichain, for every fixed \(c>c_0\),
every \(\varepsilon>0\), and every fixed \(\Lambda>16\),
the conclusion of (N.sourcefamily) holds with \(c\log x\) in place
of \((10431/1000)\log x\). More precisely, the same fixed score
\(W\) and root pool admit sources satisfying
\[
 \begin{split}
 S_X&\subseteq[X,R_XX)\cap\{x:\tau_1(x)\le c\log x\},
       \qquad 0\le a_x\le1/x,\\
 W-\varepsilon&\le\mathscr A_X\le
                    \sum_{x\in S_X}a_xH_{k(X)}(x),\\
 R_X&<\Lambda,\quad R_X\longrightarrow16,\quad
 k(X)\longrightarrow\infty,\quad3^{k(X)}/X\longrightarrow0.
 \end{split}                                         \tag{N.everyclock}
\]
One finite graft and its schedules are fixed before all sufficiently
large real \(X\). They may depend on \(c,\varepsilon,\Lambda\);
the root pool and \(W\) do not.

*Proof.* We check each estimate affected by the new parameter. Fix a
rational \(0<\theta\le1/1000\), put \(\delta=\theta/20\),
choose rational centers (S.centers), and choose concentration constants
\(C_{\delta/4},c_{\delta/4}\) at tolerance \(\delta/4\), with an integer
\(L\ge1\) satisfying \(c_{\delta/4} L>10\). Use the decidable inner
selectors (S.innercorridor) in the transition and macroblocks.
Retain the stopped law,
\(\beta=1/8\), global precisions (S.precision), and seed families.
Use the same macro schedule with this \(L,\delta\), and replace
every appended marker level by \(\lceil\theta B\rceil\).
All these choices precede the splice.

At a splice \(t\), retain \(E=\lfloor\sqrt{b_t}\rfloor\),
\(B_0=\lfloor E/4\rfloor\), and \(Q=2b_t\), and take
\(k_0=\lceil\theta B_0\rceil\). The transition rejection bound
(G.transitionfailure) holds with the new concentration constants.
Eventually
\[
 B_0\ge\sqrt{b_t}/16,\quad
 k_0\ge\theta\sqrt{b_t}/16\ge1,\quad
 B_0(E-1)+k_0\le Q.
\]
The unchanged incoming capacity is therefore available at \(Q\).
The two substitutions and rejected mass in (G.transitiondebit) give
\(D_t^{\rm tr}\le C_{\rm tr}(\theta)P_tb_t^{-3}\to0\),
using the same exponential-series bounds as before. The offsets and
slopes have not changed, so (G.offsetabsorption) still proves physical
realization of every compatible branch at a sufficiently late splice.

The new transition and macro corridors still sum to (G.totalcorridor).
Since \(2\delta<1\), the appended tag count is at most
\((B+1)^2\), and the full capacity remains (G.hybridcapacity),
including its incoming multiplier \(P_t\). At a macro start put
\(B'=B+\ell(B)\), \(k=\lceil\theta B\rceil\),
\(k'=\lceil\theta B'\rceil\), and \(q(B)=k'+h_B\).
The same depth bound gives
\[
 q(B)\le\theta B+4002(L+1)\log^2(B+2)\le B/2
 \quad\bigl(B\ge[400000(L+1)]^2\bigr).
\]
Indeed \(\theta\le1/1000\), so the explicit boundary calculation
following (G.tailconstants) applies. With
\[
 K_{\rm var}(\theta)=\frac83(C_*+1)
       \bigl(2C_6\theta^{-6}+L+1+C_{\delta/4}\bigr),
\]
the increment is at most \(K_{\rm var}(\theta)P_tB^{-4}\).
Consequently the combined transition and continuation error is at most
\[
 \Delta_t(\theta)=D_t^{\rm tr}
                 +3K_{\rm var}(\theta)P_tB_0^{-3}\longrightarrow0.
                                                        \tag{N.paramgraft}
\]
The crucial incoming-factor estimate is unchanged:
\[
 P_tB_0^{-3}\le4096C_{\rm in}b_0^{-3/2}(t+1)^3
                         (g/\gamma^{3/2})^t\longrightarrow0,
 \qquad \gamma^3-g^2=16263/8000000>0.
\]
Thus one sufficiently late common splice meets any prescribed positive
pool tolerance. The constants may grow as \(\theta\downarrow0\);
only a fixed positive \(\theta\) is being used in this limit.

Now take \(b=\lfloor\theta B\rfloor\),
\(k=\lceil\theta B\rceil\), and \(K=e_b\) at the terminal
stage. The state (G.terminalstate) holds with the new \(\delta\)
and fixed prefix constants. Since \(\mu_Y-\delta>4\theta\),
every central endpoint satisfies \(y\ge16^b\) eventually. Use the
same terminal barriers, radii and common intervals (N.common). Their width is
\[
 D(B)-A(B)\ge
       \bigl((458/1000)\theta-2\delta\bigr)B-O(1)
       =\frac{179}{500}\theta B-O(1).                \tag{N.paramroom}
\]
Floors and ceilings now give \(b'-b\le\theta\ell(B)+1\);
the changes in both interval endpoints are still \(O_\theta(\log B)\).
The positive linear width implies consecutive overlap, and both endpoints
tend to infinity by the same bound on \(a(B)\). These intervals
therefore cover a half-line at this fixed \(\theta\).

The selected-shift partition still has at most \(2b+1\le B\)
groups eventually. Since \(k\le b+1\), its level is
\(q=h_b+k\le(13/5)b+1\le B/2\) eventually. Formula (N.payment)
therefore holds literally with the new \(b,k\). Its right side is
\(O_\theta(P_tB^{-3})\) plus polynomial factors times exponentials
decaying in \(\theta B\): use \(k\ge\theta B\) and
\(b\ge\theta B/2\) eventually. It tends to zero uniformly over
the fixed pool and every cutoff in the selected interval. This retains
both marker costs and the cost of the parent-dependent choice.

Compression, its injection with a retained fan index, and (N.charge)
are unchanged. The actual radius is still \(16/(1-8^{-b})\to16\).
The ceiling bound \(k\le b+1\) gives (N.precision), so
\(3^k/X\to0\) and \(k\to\infty\). The reduced source is
still at least its parent eventually. Its terminal ordinary step cost
is at most \((481/100)b\le(481/100)\theta B\), hence uniformly
\[
 \limsup\frac{\tau_1(x)}{\log x}\le c_\theta:={
       \mu_R+\theta/20+(481/100)\theta\over
                   (\log2)(\mu_Y-\theta/20)}.
                                                        \tag{N.paramclock}
\]
Using (S.means) and \(\mu_Y\ge3\) yields
\[
 0<c_\theta-c_0
 =\theta\frac{(1+c_0\log2)/20+481/100}
                  {(\log2)(\mu_Y-\theta/20)}<3\theta.
                                                        \tag{N.parammargin}
\]
For the strict last bound, \(\log(4/3)>2/7>3/11\) implies
\(c_0<11\), and \(2/3<\log2<7/10\). The numerator of the
last fraction is less than \(1049/200\), whereas three times its
denominator exceeds \(6-1/10000>1049/200\). Choose the fixed
rational \(\theta\) also to satisfy \(3\theta<c-c_0\).
Then \(c_\theta<c\), so one eventual threshold gives the literal
clock \(c\log x\) for every later reduced source.

Finally choose one splice meeting the first half of the desired normalized
mark tolerance, using (N.paramgraft), and then a stage threshold meeting
the terminal half by (N.payment). Enlarge the latter for the common
half-line, radius, size, and clock bounds. The proof of (N.sourcefamily)
now gives (N.everyclock) for every real cutoff beyond one threshold.
The seed, persistent pool and score were fixed before \(\theta\),
so none depends on \(c\). \(\square\)

### Sources reaching a fixed target

**Theorem (fixed-target source families).** Let \(y_\star>0\) be a fixed
integer. Suppose a nonempty finite odd pool satisfies (G.marks) and
(W.antichain), and each root has a specified finite ordinary path to
\(y_\star\). Retain the same mixing hypothesis as in (N.everyclock).
For every fixed \(c>c_0\), every \(\varepsilon>0\), and every
\(\Lambda>16\), every conclusion of that theorem holds with
\(\mathcal G_c(y_\star)\) in place of \(\mathcal G_c\):
\[
 \begin{gathered}
 S_X\subseteq[X,R_XX)\cap\mathcal G_c(y_\star),\qquad 0\le a_x\le1/x,\\
 W-\varepsilon\le\mathscr A_X\le\sum_{x\in S_X}a_xH_{k(X)}(x),\\
 R_X\to16,\qquad k(X)\to\infty,\qquad3^{k(X)}/X\to0.
 \end{gathered}
                                                        \tag{N.targetfamily}
\]
The pool, target and score precede \(c\); the graft and cutoff may depend
on \(c,\varepsilon,\Lambda\). No convergence of \(y_\star\) is assumed.

*Proof.* The seed realization, variation and graft proofs are uniform for
all odd roots above \(16^{b_0}\). Let \(T_{\mathcal R}\) now be the
maximum of the specified root-to-target path lengths. Concatenation gives
\(\tau_{y_\star}(x)\le A+d+T_{\mathcal R}\) for a word of total
valuation \(A\) and length \(d\). Thus the second line of
(G.terminalstate) and (N.central) holds with \(\tau_{y_\star}\) and
this finite additive constant; all source-size bounds are unchanged.

The terminal selector, shift partition and two marker error bounds depend on
those size bounds and incoming capacity. Their proofs are unchanged.
Nonrecurrence gives a unique root visit and hence the same complete
valuation word and deterministic cuts. After the same compression
identification, (W.poolcharge) supplies (N.charge); the finite-image
injection still supplies (N.fancharge).

The reduced source is at least its parent eventually, and its terminal
ordinary cost is still bounded by \((481/100)\theta B\). Consequently
(N.paramclock) holds for \(\tau_{y_\star}\), with precisely the same
\(c_\theta\). Choose \(3\theta<c-c_0\) and apply (N.parammargin).
The finite target-path cost disappears in that ratio. All interval
overlap, radius and precision statements concern the same constructed
sources, so the final assembly proves (N.targetfamily). \(\square\)

### Why the present estimates stop short of the endpoint {#endpoint_scope}

Every fixed \(\theta>0\) gives \(c_\theta-c_0>0\) in
(N.parammargin). Taking \(\theta\) smaller controls this upper-bound
gap but does not remove it. Setting \(\theta=0\) would instead give
\(b=k=0\), outside the terminal construction, and \(\delta=0\),
outside its positive-tolerance concentration estimates. It also removes
the positive linear width in (N.paramroom), the parameterized form of
(N.room), which makes consecutive cutoff intervals overlap.

The graft constants contain \(\theta^{-6}\), and the limiting arguments
fix \(\theta\) before the splice and cutoff. A shrinking-parameter
construction would require additional uniform control of these errors,
coverage and clock slack. The common lower-density bound for \(c>c_0\)
does not supply that control or pass automatically to \(c=c_0\).
 The nonquantitative diagonal consequence
(D.vanishingclock) does give an unspecified vanishing clock loss; it
requires no uniform shrinking-parameter estimates.

### From source families to density

The result above gives the precise interval coverage, aggregate source
weights and ordinary clock needed for counting. Its mixing and
persistent-mark premises are inherited
through (G.marks). We now establish those premises, then return to this
source family to derive the explicit density bound.

## 6. Explicit reference mixing from primitive Fourier decay {#chapter06}

The construction compares reference densities at different ternary levels.
We now bound the error in replacing a finer distribution by the uniform
lift of a coarser one. The explicit Fourier-decay theorem proved in Appendix E
supplies the input. The Fourier decomposition below gives a bound valid
at every finer level; we then optimize its auxiliary parameter.
This error bound controls both the continuing seed construction and the
final conversion from marked mass to source weight.

### The primitive theorem and the quantitative target

Use the reference law \(\mu_n\) of (T.law).
For a function \(p:G_n\to\mathbb C\), set

\[
\widehat p(\xi)=\sum_{x\in G_n}p(x)e^{2\pi i\xi x/3^n}.
\]

The Fourier transform is unnormalized. A frequency
\(\xi\in G_n\) is primitive when \(3\nmid\xi\). We first work with any
fixed real \(C\ge1\) satisfying the following input:

\[
 |\widehat{\mu_n}(\xi)|\le C n^{-6409}
 \quad(n\ge1,\ \xi\in G_n,\ 3\nmid\xi).                 \tag{M.primitive}
\]

The canonical numerical choice of \(C\) and the local theorem asserting
this input are given in the final subsection. The proofs up to that
instantiation are uniform in every such \(C\).

Write \(h=\log2\), \(\gamma=\log(4/3)\), \(\lambda=\log3/\log2\), and fix

\[
 D=C20^{6409},\quad C_6=2D+2,\quad
 m_0=2^{80},\quad A=2314/25.
                                                               \tag{M.constants}
\]

For real \(80\le v\le679/5\), put

\[
 a(v)=6407-\tfrac12hv^2,\qquad q_v=hv,
\]
\[
 E_v(x)=2D x^{-a(v)}
 +\frac{32}{q_v^2\log x}x^{1-q_v}
 +2x^{-q_v}+2x^{-q_v-1}\qquad(x\ge m_0).               \tag{M.widthbound}
\]

The target is, for every integer \(1\le m\le n\),

\[
 \operatorname{Osc}(m,n):=
 \sum_{x\in G_n}|\mu_n(x)-3^{m-n}\mu_m(x\bmod3^m)|
 \le\epsilon_m,                                      \tag{M.target}
\]
\[
 \epsilon_m=
 \begin{cases}
 \min\{2,C_6m^{-A}\},&m<m_0,\\
 \min\{2,C_6m^{-A},\min_{80\le v\le679/5}E_v(m)\},&m\ge m_0.
 \end{cases}                                         \tag{M.envelope}
\]

Uniform lifting divides each probability at level \(m\) equally among
its \(3^{n-m}\) refinements at level \(n\). Thus
\(\operatorname{Osc}(m,n)\) is the sum of absolute differences from that
lift. The *mixing envelope* \(\epsilon_m\) bounds this error for every
finer level at once.

All logarithms in this section are natural. The coefficient \(C\) is
fixed first. The width \(v\) is fixed during each proof, but every estimate
has the same displayed cutoff throughout its compact range. Consequently
one may optimize \(v\) at a fixed coarse level \(m\); it never depends
on a physical source or on a subsequent counting cutoff.

### A head selected by its first crossing

Fix \(n\ge m_0\), write \(L=\log n\), and use independent valuations
\(\Pr(K_i=a)=2^{-a}\), \(a\ge1\). Put \(S_i=\sum_{j\le i}K_j\), \(S_0=0\).
For a word \(w=(k_1,\ldots,k_d)\), define its dyadic offset and its
integer cleared offset by

\[
 C(w)=\sum_{i=1}^d3^{i-1}2^{-S_i},\qquad
 B(w)=2^{S_d}C(w)=\sum_{i=1}^d3^{i-1}2^{S_d-S_i}.       \tag{M.offset}
\]

Here the \(S_i\) are the partial sums of that word. The empty offset is
zero. For concatenated words \(w,t\), direct splitting gives

\[
 C(wt)=C(w)+3^{|w|}2^{-S_{|w|}}C(t).                  \tag{M.split}
\]

This is the inverse-prefix orientation of (T.law).

A word is \(v\)-typical at ambient length \(n\) if every nonempty
contiguous subword of length \(r\) has valuation sum within
\(v(\sqrt{rL}+L)\) of \(2r\). Let \(F_{n,v}\) be the failure of this
condition for the full length-\(n\) word. Set

\[
 Q=\lambda n-v^2L.
                                                               \tag{M.gatelevel}
\]

For \(0\le k<n\) and \(0\le l<2n\), the \((k,l)\) head family consists
of typical words of length \(d=k+1\), total \(S_d=l\), with
\(S_k\le Q<S_{k+1}\). Positivity of the valuations makes this crossing
unique. The remaining tail keeps its unrestricted law.

We record explicitly why these families cover every globally typical word
and why their residue maps are injective at the common cutoff.

**Lemma (common scalar margins).** Throughout \(80\le v\le679/5\) and
\(n\ge m_0\), one has \(L>4\) and

\[
 ((3/2)v^2+v)L\le(3/200)n,\qquad
 ((5/2)v^2+v)L\le(3/10)n.                             \tag{M.logbudgets}
\]

Also \(1<\lambda<8/5\),
\(693/1000<h<347/500\), and \(2/7<\gamma<1/3\).

*Proof.* The logarithmic bounds follow, for example, from the positive
series
\[
 \log\frac{1+t}{1-t}
 =2\sum_{j\ge0}\frac{t^{2j+1}}{2j+1}\quad(0<t<1),
                                                               \tag{M.logseries}
\]
obtained by integrating the geometric series. At \(t=1/3\), ten terms
give a lower bound \(H_-\), and the omitted tail is at most
\[
 \frac{2\,3^{-21}}{21(1-1/9)}.
\]
Direct rational comparison gives
\[
 693/1000<H_-<h<H_+:=H_-+
 \frac{2\,3^{-21}}{21(1-1/9)}<693147181/10^9<347/500.
                                                               \tag{M.logbounds}
\]
At \(t=1/7\), the first term gives \(\gamma>2/7\); the upper bound
follows from \(\log(1+1/3)<1/3\). Finally \(3>2\) and \(3^5<2^8\)
give the bounds on \(\lambda\).

For \(x>0\), \(\log x\le\sqrt x\). Indeed, with \(z=\sqrt x/2\),
\(\log z\le z-1\) and \(\log2\le1\) imply this inequality.
For \(n\ge2^{80}\), therefore \(L\le\sqrt n\) and
\(\sqrt n\ge2^{40}\). Both coefficients in (M.logbudgets) increase with
\(v\). The exact comparisons
\[
 (3/2)136^2+136<(3/200)2^{40},\qquad
 (5/2)136^2+136<(3/10)2^{40}
\]
prove the result. Also \(L\ge80h>4\). \(\square\)

**Lemma (head location).** Every globally typical word has a unique
head in the families above. Every nonempty head family satisfies

\[
 20k\le17n,\qquad
 Q<l\le Q+2vL<2n.                                    \tag{M.headlocation}
\]

*Proof.* The second budget implies \(v^2L\le n\), so \(Q>0\).
The inequality
\[
 v\sqrt{sL}\le s/10+(5/2)v^2L
                                                               \tag{M.youngindex}
\]
follows by completing a square. Applied with \(s=n\), typicality and
(M.logbudgets) give \(S_n\ge(8/5)n>Q\). Thus there is a unique first
crossing at a depth \(k+1\le n\), and its prefix is typical.

For a nonempty head, typicality of its prefix of length \(k\) and
\(S_k\le Q\) give, when \(k>0\),
\[
 (19/10)k\le\lambda n+((3/2)v^2+v)L
 <(323/200)n.
\]
Hence \(20k<17n\). The case \(k=0\) also satisfies the asserted bound.
The last valuation is at most \(2+v(\sqrt L+L)\le2vL\):
use \(\sqrt L\le L/2\), \(L\ge4\), and \(v\ge17\).
Consequently \(l\le Q+2vL=\lambda n-v(v-2)L<2n\).
This proves both coverage and the stated finite index ranges. \(\square\)

**Lemma (small cleared offset).** Every head satisfies

\[
 0<B(w)<3^n.                                        \tag{M.headsmall}
\]

*Proof.* Its prefix sums obey \(S_i\ge2i-v(\sqrt{iL}+L)\). Therefore,
writing \(j=i-1\),
\[
 B(w)\le2^{l-2}\sum_{j=0}^{d-1}
  \exp\{-\gamma j+hv(\sqrt{(j+1)L}+L)\}.
\]
Completing a square once more gives
\[
 hv\sqrt{(j+1)L}
 \le(3\gamma/4)(j+1)+\frac{h^2v^2L}{3\gamma}.
\]
The remaining geometric sum is at most
\((1-e^{-\gamma/4})^{-1}<16<e^{16}\). For the first inequality,
\(\gamma/4>1/14\) and \(e^{1/14}\ge1+1/14>16/15\) suffice.
With \(l\le\lambda n-v^2L+2vL\), it follows that
\[
 B(w)<3^n\exp\{Q_*(v)L+K_*\},
\]
\[
 Q_*(v)=v^2\left(-h+\frac{h^2}{3\gamma}\right)+3hv,
 \qquad K_*=-2h+3\gamma/4+16.                         \tag{M.headmargin}
\]
The bounds in (M.logbounds) give
\[
 -h+\frac{h^2}{3\gamma}<-\frac{196637}{1500000},
 \qquad
 Q_*(v)<-\frac{196637}{1500000}v^2+\frac{1041}{500}v.
\]
The displayed quadratic is decreasing for \(v\ge80\) and is less than
\(-672\) at 80. Also \(K_*<17\). Since \(L>4\), the exponent is negative.
Positivity of every summand proves the lower bound. \(\square\)

**Lemma (head injection and its second moment).** At fixed \(d,l\), the
map from a head to \(C(w)\bmod3^n\) is injective. Let \(p_{k,l}\) be the
nonnegative sub-probability mass function on \(G_n\) obtained by mapping
the \((k,l)\) head family with its original iid weights. Then

\[
 \sum_{y\in G_n}p_{k,l}(y)^2\le2^{-l}.                \tag{M.headL2}
\]

*Proof.* We first show that \(B(w)\), together with \(d,l\), determines
the word. For \(d=1\), its only valuation is \(l\). For \(d\ge2\),
\[
 B(w)-3^{d-1}=2^{k_d}B(k_1,\ldots,k_{d-1}).
\]
The shorter cleared offset is odd: its last summand is odd and every
earlier summand is even. Thus \(k_d\) is exactly the 2-adic valuation of
the positive left side. Divide by \(2^{k_d}\), reduce the total from \(l\)
to \(l-k_d\), and induct.

Equality of the source residues, multiplied by the common unit \(2^l\),
gives equality of the cleared offsets modulo \(3^n\). By (M.headsmall)
they are equal as integers, and the preceding decoding applies. Each
accepted head has probability exactly \(2^{-l}\). Injection makes every
occupied atom of \(p_{k,l}\) equal to \(2^{-l}\); hence its squared sum is
\(2^{-l}\sum_y p_{k,l}(y)\le2^{-l}\). Empty families give zero. \(\square\)

### Tail levels and the squared Fourier estimate

For any real vector \(p\) on \(G_n\), define its uniform fiber average
and its oscillation by

\[
 (\mathsf A_{m,n}p)(x)=3^{m-n}
   \sum_{y\equiv x\ (3^m)}p(y),\qquad
 \mathsf O_{m,n}(p)=\|p-\mathsf A_{m,n}p\|_1.
                                                               \tag{M.average}
\]

Projectivity makes \(\mathsf O_{m,n}(\mu_n)=\operatorname{Osc}(m,n)\).
The averaging map is positive, mass-preserving and L1-contracting.
For real vectors \(p,t\) and convolution
\((p*t)(x)=\sum_y p(y)t(x-y)\), the following finite
identity is the precise use of Fourier cancellation.

**Lemma (finite collision bound).** If \(1\le m\le n\) and
\(|\widehat t(\xi)|\le\delta\) at every frequency not divisible by
\(3^{n-m}\), with \(\delta\ge0\), then

\[
 \mathsf O_{m,n}(p*t)^2\le
 \delta^2 3^n\sum_y|p(y)|^2.                          \tag{M.collision}
\]

*Proof.* The geometric character sum on a fiber shows that the Fourier
transform of \(\mathsf A_{m,n}\) keeps exactly the frequencies divisible
by \(3^{n-m}\), and sets all others to zero. Orthogonality of the same
characters gives Parseval in the present normalization:
\(\sum_\xi|\widehat p(\xi)|^2=3^n\sum_y|p(y)|^2\).
Also \(\widehat{p*t}=\widehat p\,\widehat t\), by changing variables in
the finite double sum. If \(z=p*t-\mathsf A_{m,n}(p*t)\), these identities
and Cauchy--Schwarz give
\[
 \|z\|_1^2\le3^n\sum_y|z(y)|^2
 =\sum_{3^{n-m}\nmid\xi}|\widehat p(\xi)\widehat t(\xi)|^2
 \le\delta^2\sum_\xi|\widehat p(\xi)|^2.
\]
This proves the claim, including the empty discarded-frequency set when
\(m=n\). \(\square\)

Now assume \(9n\le10m\le10n\) and consider a nonempty \((k,l)\) head
family. Its length \(d=k+1\) satisfies \(d\le m\): by (M.headlocation),
\(m-k\ge n/20\ge1\). Set \(T=n-d\). Let \(t_{k,l}\) be the law on \(G_n\)
of \(3^d2^{-l}C_T\), using the remaining independent \(T\) valuations.
The selected full-word submass is exactly
\[
 c_{k,l}=p_{k,l}*t_{k,l}.                            \tag{M.convolution}
\]
Indeed, (M.split) has this form, and the tail is unrestricted and
independent of the head; all heads in this slice have the same \(d,l\).

For a discarded frequency, choose its nonzero representative and put
\(t=\nu_3(\xi)<n-m\). Multiplication by \(2^{-l}\) preserves this
valuation. Since \(d\le m\), one has \(t<T\). The character applied to
\(3^d2^{-l}C_T\) has conductor \(3^r\), where
\[
 r=T-t\ge m-k\ge n/20.                               \tag{M.tailconductor}
\]
Projectivity identifies its expectation with a primitive Fourier
coefficient of \(\mu_r\), at a unit frequency; hence (M.primitive) yields
\[
 |\widehat t_{k,l}(\xi)|\le Cr^{-6409}
 \le Dn^{-6409}.                                    \tag{M.taildecay}
\]
The conductor bound gives the factor \(20^{6409}\).

**Proposition (general-width high-regime estimate).** For
\(80\le v\le679/5\), \(n\ge m_0\) and \(9n\le10m\le10n\),
\[
 \operatorname{Osc}(m,n)
 \le2Dn^{-a(v)}+2\Pr(F_{n,v}).                       \tag{M.high}
\]

*Proof.* By (M.collision), (M.headL2) and (M.taildecay),
\[
 \mathsf O_{m,n}(c_{k,l})^2
 \le D^2n^{-12818}3^n2^{-l}
 <D^2n^{-12818+hv^2},
\]
where the strict crossing \(l>Q=\lambda n-v^2L\) gives
\(3^n2^{-l}<n^{hv^2}\). Taking the square root preserves half the
entropy exponent, before summing any slices.

The first-crossing head events for different \((k,l)\) are disjoint.
Their union includes all globally typical words by (M.headlocation).
Consequently
\[
 \mu_n=\sum_{k<n,\ l<2n}c_{k,l}+b,\qquad
 b\ge0,\quad\sum_y b(y)\le\Pr(F_{n,v}).
\]
There are at most \(2n^2\) slices. An empty slice contributes zero.
Linearity of averaging, the triangle inequality, and
\(\mathsf O_{m,n}(b)\le2\|b\|_1\) prove (M.high).
The prefix families have not been normalized by their success masses.
\(\square\)

### The reference rejection probability

The preceding decomposition has isolated the rejected mass. We now bound
that mass directly under the reference law, without charging all interval
lengths at their worst common rate.

**Lemma (geometric log-MGF at its pole).** Put \(X=K-2\) and
\(c=1/h\). Define \(g(s)=\log\mathbb E e^{sX}\) for every real \(s<h\).
For \(0\le\theta<h\),
\[
 g(\theta):=\log\mathbb E e^{\theta X}
 =-\theta-\log(2-e^\theta)
 \le\frac{\theta^2}{1-c\theta}.
                                                               \tag{M.mgf}
\]
For every \(\theta\ge0\), \(g(-\theta)\le\theta^2\).

*Proof.* Summing the geometric series gives the equality. One has
\(g(0)=g'(0)=0\) and
\(g''(\theta)=2e^\theta/(2-e^\theta)^2\). For
\(H(\theta)=\theta^2/(1-c\theta)\), \(H''=2/(1-c\theta)^3\).
Their ratio is
\[
 R(\theta)=\frac{e^\theta(1-c\theta)^3}{(2-e^\theta)^2}.
\]
It starts at one and is nonincreasing if
\[
 F(\theta)=3c(2-e^\theta)-(1-c\theta)(2+e^\theta)\ge0.
\]
On \([0,h]=[0,1/c]\), \(F(0)=3(c-1)>0\), \(F(h)=0\), and
\(F''(\theta)=-e^\theta(c+1-c\theta)<0\).
Concavity proves \(F\ge0\), hence \(g''\le H''\). Integrate twice from
zero. For the other sign, \(g''(-\theta)\le2\) for \(\theta\ge0\);
the same integration gives \(g(-\theta)\le\theta^2\). \(\square\)

**Lemma (two-sided sum bound).** For \(r\ge1,z>0\) and independent
copies \(X_1,\ldots,X_r\),
\[
 \Pr\{|\textstyle\sum_{i=1}^rX_i|
          \ge2\sqrt{rz}+cz\}\le2e^{-z}.               \tag{M.chernoff}
\]

*Proof.* For either sign apply the exponential Markov inequality at
\(\theta=s/(1+cs)<h\), \(s=\sqrt{z/r}\).
The log-MGF bound gives exponent
\(-\theta(2\sqrt{rz}+cz)+r\theta^2/(1-c\theta)=-z\).
Add the two tails. \(\square\)

**Proposition (length-sensitive failure).** With \(q=vh\) and \(L=\log n\),
\[
 \Pr(F_{n,v})\le
 \frac{16}{q^2L}n^{1-q}+n^{-q}+n^{-q-1}.              \tag{M.failure}
\]

*Proof.* For an interval of integer length \(1\le r\le L\), use
\(z=qL+(q/2)\sqrt{rL}\) in (M.chernoff). Writing
\(s=\sqrt{r/L}\le1\), its threshold divided by \(L\) is at most
\[
 2s\sqrt{q+(q/2)s}+c(q+(q/2)s)
 \le v+s(2\sqrt{3q/2}+v/2)\le v(1+s).
\]
The last inequality is equivalent to \(v\ge24h\), valid on the stated
range. Thus failure of this interval's typicality has probability at most
\(2n^{-q}e^{-(q/2)\sqrt{rL}}\). There are at most \(n\) starts at each
length. The decreasing-integrand comparison and substitution \(u=\sqrt{xL}\)
give
\[
 \sum_{r\ge1}e^{-(q/2)\sqrt{rL}}
 \le\int_0^\infty e^{-(q/2)\sqrt{xL}}\,dx
 =\frac8{q^2L}.
\]
This proves the first term in (M.failure).

For \(r>L\), use \(z=(q+2)L\). Its threshold is at most
\(v(\sqrt{rL}+L)\), because
\[
 v\ge2\sqrt{q+2}+2c.
\]
To check this uniformly, use \(h<7/10\), \(c<3/2\);
\((v-3)^2>4((7/10)v+2)\) at \(v=80\), with positive derivative thereafter.
Each long interval therefore fails with probability at most
\(2n^{-q-2}\). Bounding their number by the total \(n(n+1)/2\) gives the
remaining two terms. The strict failure events are contained in the
non-strict tail events just estimated. \(\square\)

Combining (M.high) and (M.failure) gives
\[
 \operatorname{Osc}(m,n)\le E_v(n)
 \quad(n\ge m_0,\ 9n\le10m\le10n).                    \tag{M.localmixing}
\]

### From nearby levels to the full compact envelope

For \(m\le r\le n\), projectivity and uniform lifting give
\[
 \operatorname{Osc}(m,n)\le
 \operatorname{Osc}(m,r)+\operatorname{Osc}(r,n).      \tag{M.triangle}
\]
To see the normalization, insert \(3^{r-n}\mu_r\) between the two
vectors defining \(\operatorname{Osc}(m,n)\). The second difference is
the uniform lift of
\(\mu_r-3^{m-r}\mu_m\), whose L1 norm is unchanged.

Every power appearing in (M.widthbound) exceeds 8 throughout the width
range. Indeed \(a(v)\ge a(679/5)>8\) by (M.logbounds), and
\(q_v-1\ge80H_--1>8\). The positive terms are decreasing in \(x\).
Since \((11/10)^8>2\),
\[
 2E_v((11/10)x)<E_v(x)\quad(x\ge m_0),                \tag{M.contraction}
\]
also for the term with \(1/\log x\), which is decreasing.

**Theorem (all high levels).** For every fixed permitted width,
\[
 \operatorname{Osc}(m,n)\le E_v(m)
 \quad(n\ge m\ge m_0).                               \tag{M.allhigh}
\]

*Proof.* Induct on \(n-m\), simultaneously for all pairs. The equal case
is zero. Put \(r=\lfloor10m/9\rfloor\). Since \(m\ge m_0>90\),
\(r\ge(11/10)m>m\). If \(n\le r\), (M.localmixing) and monotonicity
give \(E_v(n)\le E_v(m)\). Otherwise \(m<r<n\): apply (M.localmixing)
to \((m,r)\), the induction hypothesis to \((r,n)\), and then
(M.triangle)--(M.contraction). The result is at most
\(2E_v(r)\le2E_v((11/10)m)<E_v(m)\).
The induction uses the geometric sequence of intermediate levels.
\(\square\)

**Theorem (full quantitative mixing).** The target (M.target) with the
envelope (M.envelope) holds. In particular
\[
 \operatorname{Osc}(m,n)\le C_6m^{-2314/25}
 \le C_6m^{-92}\le C_6m^{-6}\quad(1\le m\le n).         \tag{M.powers}
\]

*Proof.* Take \(v_*=6749/50\). The rational bounds in (M.logbounds) give
\[
 6407-\tfrac12v_*^2H_+>2314/25,\qquad
 v_*H_--1>2314/25.
                                                               \tag{M.exponentguards}
\]
For \(m\ge m_0\), (M.allhigh) therefore implies
\[
 \operatorname{Osc}(m,n)
 \le m^{-A}\left(2D+\frac{32}{q_{v_*}^2\log m}
                  +\frac2m+\frac2{m^2}\right)
 <(2D+2)m^{-A}=C_6m^{-A}.
\]
The bracket after \(2D\) is less than two already with
\(q_{v_*}>80(693/1000)>55\), \(\log m>4\), and \(m\ge2^{80}\).
For \(m<m_0\), both compared vectors are probability masses, so
\(\operatorname{Osc}(m,n)\le2\). On the other hand \(C\ge1\) and \(A<100\)
give
\[
 C_6>2\,20^{6409}>2^{25637}>2^{8001}>
 2(2^{80})^A.
\]
Thus \(2<C_6m^{-A}\) also in this range.

For each fixed \(m\ge m_0\), \(v\mapsto E_v(m)\) is continuous on the
closed interval \([80,679/5]\), so it attains its minimum. All its values
are bounds for the same \(\operatorname{Osc}(m,n)\); take their minimum
along with the power bound and the universal bound two. This proves
(M.envelope). The two weaker powers follow from \(m\ge1\).
\(\square\)

For the paper's normalized markers the exact identity is
\[
 \left\langle|\rho_n-\rho_m\circ\pi_{n,m}|\right\rangle_n
 =\frac23\operatorname{Osc}(m,n)\le\frac23\epsilon_m.   \tag{M.marker}
\]
This discharges (T.mix) for the complete retained envelope, and also its
sixth-order specialization used in the finite graft and terminal source
sections. The order-92 seed variation bound and the later density
optimization use the stronger statements with the same \(C_6\).


### The explicit coefficient

The finite recipe in (E.recipe) specifies our coefficient:
\[
 C_{\rm primitive}:=C_{6409}^{\rm loc}\ge1.           \tag{M.canonicalC}
\]
**Theorem (primitive input).** This coefficient satisfies (M.primitive).

*Proof.* Apply (E.primitive) at \(B=6409\).
Its law is (T.law), its transform is unnormalized, its frequencies are
precisely those not divisible by three, and it covers every positive level.
\(\square\)

Together with the preceding uniform-in-\(C\) conversion, this fixes
\(D=C_{\rm primitive}20^{6409}\) and \(C_6=2D+2\) for the seed, root-score
and density recipes. The coefficient and all startup choices precede the
physical counting cutoff and the chosen clock.

For comparisons only, (E.mazur-coefficient) preserves the earlier source
integer \(C_{\rm primitive}^{\rm Maz}\). The adapter in [3] is
\[
 C_{\rm Maz}=2C_{\rm primitive}^{\rm Maz}20^{6409}+2+2^{481}>C_6.
                                                               \tag{M.sourceadapter}
\]
The strict comparison follows from (E.coefficientcomparison). Section 11 compares against this fixed coefficient. Appendix A compares
fixed-depth and first-crossing seeds at a common primitive coefficient.

Appendix E uses the pairing and separated-triangle method of [1, Section 7]
and [3]. The preceding argument converts its coefficient into the envelope
(M.envelope), used by the seed and counting constructions.

## 7. Seed marks and variation bounds uniform over roots {#chapter07}

We return to the seed families defined in the continuation construction.
Their reference average can be evaluated exactly, but an average at one
stage does not guarantee that any fixed root keeps a positive mark later.
Using the preceding mixing estimate, we bound the total change at each
root over all subsequent stages. The next section combines this variation
bound with positive reference survival to choose the required fixed roots.

### The finite mark and its exact normalization

Fix an integer \(b=b_0\ge32^5\). Use the fixed-depth seed families
(G.fixedseed), with
\[
 b_{j+1}=b_j+\lfloor b_j/100\rfloor,\quad
 m_j=\lceil b_j^{3/5}\rceil,\quad
 a_j=\lfloor b_j/4\rfloor.                            \tag{B.parameters}
\]
Thus \(V_j=\{w:|w|=b_j,\ |A(w)-2b_j|\le m_j\}\). Set
\[
 p_j=\sum_{w\in V_j}2^{-A(w)},\qquad
 D_N=\sum_{j<N}b_j,\quad q_N=D_N+a_N.                 \tag{B.conductor}
\]
Every \(V_j\) is prefix-free, so \(0\le p_j\le1\).
For \(N\ge0\), concatenate one word from each \(V_0,\ldots,V_{N-1}\)
and call the resulting set \(\mathcal V_N\). At \(N=0\) it contains
the empty word. The prescribed lengths determine all cuts.
The family \(\mathcal V_N\) is prefix-free, of exact length \(D_N\),
and independent reference letters give
\[
 \sum_{w\in\mathcal V_N}2^{-A(w)}=\prod_{j<N}p_j.      \tag{B.product}
\]
The product is one at \(N=0\), and zero if one chosen family is empty.

On \(G_{q_N}\) define the backward seed mark by the finite sum
\[
 g_N(y)=\sum_{w\in\mathcal V_N}\mathcal T_{w,q_N}
       (\rho_{a_N}\circ\pi_{q_N-|w|,a_N})(y).           \tag{B.mark}
\]
Here \(\mathcal T\) is (T.operator). For a word of length \(d\) and
valuation \(A\), its nonzero summand is
\(3^d2^{-A}\rho_{a_N}(z\bmod3^{a_N})\), where
\(y=C_w+3^d2^{-A}z\) in \(G_{q_N}\).
Here \(q_N-d=a_N\) for every complete seed word, so the
payload has exactly the required residual precision. No choice of a physical root occurs in this
definition, and no family is normalized by its surviving probability.

**Lemma (finite mean and support).** For every \(N\ge0\),
\[
 g_N\ge0,\quad g_N(y)=0\ (3\mid y),\qquad
 \langle g_N\rangle_{q_N}=\frac23\prod_{j<N}p_j,
 \quad
 \frac{1}{2\,3^{q_N-1}}\sum_{3\nmid y}g_N(y)=\prod_{j<N}p_j.
                                                               \tag{B.mean}
\]

*Proof.* Positivity follows from (T.operator). The full-group mean of
each summand is \((2/3)2^{-A(w)}\) by (T.norm), since lifting the marker
does not change its mean. Sum and use (B.product).
For a nonempty word, \(C_w\equiv2^{-k_1}\pmod3\), so its affine image
contains only units. For the empty word, \(a_N\ge1\) and the marker
itself vanishes on nonunits. There are exactly \(2\,3^{q_N-1}\) units;
converting the full-group mean to the unit-relative mean cancels the
factor \(2/3\). The calculation is an exact average over a complete residue period. \(\square\)

### A pointwise cap for the seed mark

The iid reversal in (T.law) gives the recursion
\[
 \rho_{r+1}(y)=
 3\sum_{\substack{a\ge1\\2^ay\equiv1\ (3)}}
       2^{-a}\rho_r\left((2^ay-1)/3\bmod3^r\right).    \tag{B.recursion}
\]
The argument is well defined for \(y\bmod3^{r+1}\). On the coset
\(y\equiv1\pmod3\), the allowed letters are even and their total
coefficient is one; on \(y\equiv2\pmod3\), they are odd and their
total coefficient is two. There are no allowed letters on the third
coset. Consequently
\[
 \|\rho_r\|_\infty\le\frac23\,2^r\qquad(r\ge0).       \tag{B.markercap}
\]
Indeed, iterate the factor-two bound starting at \(\rho_0=2/3\).

For completeness, this bound extends to a finite prefix-free stopping
tree without assuming equal leaf depths. Give each leaf a nonnegative
payload at most \(B\), and suppose the tree has maximum depth \(D\).
At a node of depth \(d\), its remaining weighted transfer is at most
\(2^{D-d}B\). A leaf has value at most \(B\le2^{D-d}B\).
An internal node is a positive sum over its allowed next letters; the
total one-letter coefficient at any residue is at most two by
(B.recursion). Downward induction therefore proves the bound at that
node. A node cannot be both a leaf and an internal node because the
family is prefix-free. Missing branches contribute zero. The induction
uses the residual level at each node; the padding in (B.mark)
ensures that every leaf payload is defined there.

Apply this argument with \(D=D_N\) and
\(B=(2/3)2^{a_N}\). It gives
\[
 0\le g_N(y)\le B_{q_N}:=\frac23\,2^{q_N}.             \tag{B.cap}
\]
Thus the cap is proved pointwise. It is not deduced from the mean.

### Realization at physical roots

For every positive odd integer \(M\ge16^b\), let \(Z_N(M)\) be the
physical mark (G.inmark), with the same complete words and cuts. Then
\[
 Z_N(M)=g_N(M\bmod3^{q_N})\qquad(N\ge0).              \tag{B.physical}
\]

To prove this, fix a word in \(\mathcal V_N\). Membership of the root
residue in its affine image is, by (T.injection), equivalent to
integrality of its full inverse endpoint and implies integrality of all
earlier endpoints. At the first block the parent is at least \(16^b\).
The local seed estimate in the proof of (G.prefix) gives a strictly
positive offset margin for every compatible word and a new endpoint at
least \(16^{b_1}\). Repeat at successive blocks. All endpoints are
positive and odd and have exactly the prescribed valuations; no further
root-dependent rejection is necessary. Equivalently, the total offset
bound \(C_w\le2^{b+1}<16^b\le M\) gives positivity at every prefix.

Conversely every physical history in \(\mathcal P_N(M)\) arises from
one such compatible complete word. Its cuts have the prescribed fixed
block lengths. Formula (T.operator) assigns exactly its actual
slope weight and endpoint marker. Summing proves (B.physical), including
the empty history at \(N=0\). Nonunit endpoints may be retained in the
physical family; their positive-level marker is zero. This changes
neither side of the identity.

### A fixed-time estimate for the valuation window

Work only on the auxiliary iid probability space. Write
\(S_B=\sum_{i=1}^B(K_i-2)\). For \(B\ge32^5\), \(m=\lceil B^{3/5}\rceil\)
satisfies
\[
 m\ge32^3,\qquad \frac mB\le2B^{-2/5}\le\frac1{512},
 \qquad \frac{m^2}B\ge B^{1/5}.                       \tag{B.widthguards}
\]
By (M.mgf) and \(1/\log2<3/2\),
\[
 \log\mathbb E e^{\theta(K-2)}
 \le\frac{\theta^2}{1-(3/2)\theta}\quad(0\le\theta<2/3),
 \qquad
 \log\mathbb E e^{-\theta(K-2)}\le\theta^2\quad(\theta\ge0).
                                                               \tag{B.mgf}
\]
Independence and Markov's inequality, with
\(\theta=m/(2B+(3/2)m)\) for the positive tail and
\(\theta=m/(2B)\) for the negative tail, give
\[
 \Pr(S_B\ge m)\le e^{-m^2/(4B+3m)},\qquad
 \Pr(S_B\le-m)\le e^{-m^2/(4B)}.                      \tag{B.fixedtime}
\]
The seed failure \(|S_B|>m\) is contained in the union of these
two events. In particular
\[
 1-p_j\le2\exp\!\left(-\frac{m_j^2}{4b_j+3m_j}\right)
 \le2\exp\!\left(-\frac{b_j^{1/5}}{4+3/512}\right).
                                                               \tag{B.failure}
\]
The positive-tail denominator includes the geometric MGF's \(3m\)
correction. No stopping-window or overshoot error term is needed for this seed.

### The increment before simplifying its constants

All reference mixing below uses the fixed coefficient \(C_6\) from
(M.constants), with (M.powers) at order 92. A generic order-six
coefficient is not sufficient. At stage \(j\), put \(B=b_j\) and
\[
 \ell=a_j=\lfloor B/4\rfloor,\quad
 k=a_{j+1}=\lfloor(B+\lfloor B/100\rfloor)/4\rfloor,
 \quad q=B+k.                     \tag{B.incrementlevels}
\]
Both marker levels are at least one and \(k\ge\ell\ge B/8\).
For the last inequality, \(\lfloor B/4\rfloor\ge B/4-1\ge B/8\)
when \(B\ge8\). Moreover
\[
 \ell\le q,\qquad
 q\le\left(1+\frac{101}{400}\right)B
       =\frac{501}{400}B<2B.                          \tag{B.paidconductor}
\]
Thus the comparison level stays within (G.incapacity)'s allowance.

Define \(L=L_{V_j,q,k}\) by (T.selected), and let
\(H^{\rm in}_{j,q}\) be the actual incoming histogram of (G.incapacity).
The same root-independent family \(V_j\) is applied to each parent.
Its affine compatibility is exactly physical realization: (G.prefix)
puts that parent at least at \(16^B\), so every compatible extension
is positive. Uniqueness of the prescribed cut and multiplication of the
slope weights then give the exact signed identity
\[
 Z_{j+1}(M)-Z_j(M)=
 \sum_{y\in G_q}H^{\rm in}_{j,q}(y)
       [L(y)-\rho_\ell(\pi_{q,\ell}y)].              \tag{B.incrementidentity}
\]
There is no conditioning or division by retained mass in this formula.
Combining (T.stopped), (G.incapacity) and (M.powers) proves, simultaneously
for every positive odd \(M\ge16^b\) and every \(j\ge0\),
\[
 |Z_{j+1}(M)-Z_j(M)|\le\frac23P_j
       \left(\frac{C_6}{k^{92}}+\frac{C_6}{\ell^{92}}+1-p_j\right).
                                                               \tag{B.rawincrement}
\]

In particular this retains the actual incoming tag factor
\(20(4b+1)(j+1)^3(2013/2000)^j\). Its capacity coefficient is
\[
 P_j=20(4b+1)(2^{b+1}+16^b)(j+1)^3(2013/2000)^j.
\]
The \(16^b\) term bounds the finite-modulus boundary error
\(3^q\omega\); it has not been discarded as a negligible asymptotic
term. The two mixing costs and the valuation-window failure are three
separate costs in (B.rawincrement).

### An every-generation majorant with the retained coefficient

Put
\[
 \alpha=100999/100000,\quad g=2013/2000,\quad
 \lambda_{\rm var}=g\alpha^{-92},\quad
 S_{92}=8\cdot465!\cdot576^{465}. \tag{B.rates}
\]
For every integer \(B\ge100000\),
\[
 B+\lfloor B/100\rfloor\ge(101/100)B-1
       \ge\alpha B.
\]
All floors in (B.parameters) meet this condition, so
\(b_j\ge b\alpha^j\). There is no omitted early-stage exception.

Since \(4+3/512<2333/100\), (B.failure) is at most
\(2e^{-b_j^{1/5}/(2333/100)}\). For \(B\ge1\), use
\(2333/100<576\), followed by the degree-465 exponential-series term, to get
\[
 2e^{-B^{1/5}/(2333/100)}
 \le8B e^{-B^{1/5}/576}
 \le8\cdot465!\,576^{465}B^{1-465/5}
 =S_{92}B^{-92}.                                    \tag{B.polynomialfailure}
\]
Also \(465!<512^{465}\) and \(576<1024\), whence
\(S_{92}<2^{8838}\). The actual coefficient in [the reference-mixing section](#chapter06) satisfies
\(C_6>2^{25637}\), so \(S_{92}<C_6\). This absorption uses the size of the coefficient; an arbitrary
mixing hypothesis without that size condition would not suffice.

Let
\[
 H_b^*=\frac23(4b+1)22(2^{b+1}+16^b).
\]
Replacing the smaller tag coefficient 20 by 22 and using
\(k,\ell\ge b_j/8\) gives
\[
 |Z_{j+1}(M)-Z_j(M)|
 \le H_b^*(j+1)^3
  \frac{2C_6\,8^{92}+S_{92}}{b^{92}}\lambda_{\rm var}^j.
                                                               \tag{B.onerate}
\]
The incoming factor \(g^j\) is included in \(\lambda_{\rm var}^j\).
Exact rational comparisons give
\[
 \frac25<\lambda_{\rm var}<\frac{41}{100}<\frac12.
                                                               \tag{B.ratebounds}
\]
Also \(4b+1\le5b\) and \(2^{b+1}\le16^b\), so
\(H_b^*\le220b16^b\). Finally
\[
 220(2\,8^{92}+1)<2^{467}.                           \tag{B.coefficientguard}
\]
Indeed \(8^{92}=2^{276}\), \(2\,8^{92}+1<2^{278}\) and
\(220<2^8\), giving even the upper bound \(2^{286}<2^{467}\).
We retain the displayed conservative coefficient for the startup recipe;
optimizing that variation coefficient is a separate question.

**Theorem (seed variation uniformly over roots).** With exactly
\[
 F_b=2^{467}b16^b(C_6+1),
\]
every positive odd \(M\ge16^b\) satisfies, at every \(j\ge0\),
\[
 \boxed{|Z_{j+1}(M)-Z_j(M)|
       \le F_b(j+1)^3\lambda_{\rm var}^j.}            \tag{B.variation}
\]

*Proof.* In (B.onerate), use \(b^{-92}\le1\), \(S_{92}<C_6\),
\(H_b^*\le220b16^b\) and (B.coefficientguard), then
\(C_6<C_6+1\). All bounds are independent of the
root and valid starting at \(j=0\). \(\square\)

Consequently \(Z_j(M)\) converges to a nonnegative limit, and for
all integers \(n\ge N\ge0\),
\[
 |Z_n(M)-Z_N(M)|\le
 F_b\sum_{j\ge N}(j+1)^3\lambda_{\rm var}^j.          \tag{B.tail}
\]
The series converges by \(0<\lambda_{\rm var}<1/2\); sum finite
increments first and then bound by its entire nonnegative tail.
The same bound holds for the limit. Nonnegativity of that limit does
not imply it is positive.

### Handoff and provenance

The exact finite mark, cap, mean and physical identity are
(B.mark)--(B.physical). The full later-generation loss is (B.tail).
To obtain (G.marks), the next step must still certify positive infinite
reference survival, choose a finite \(N\) for which the entire variation
tail fits the retained budget, and select one fixed finite convergent
root pool. [The persistent-root section](#chapter08) retains the exact residual (R.residual) and minimum
score (R.score); the full variation tail supplies persistence at the fixed roots.

The positive-level markers vanish on nonunit terminal children, which have
no further integral inverse child. This permits all positive odd histories
to be included in (B.physical). The geometric moment estimate and the mixing
bound of Section 6 give the variation bound used below.

**Coefficient scope.** The same proof of (B.variation) and (B.tail)
applies with \(C_6\) replaced throughout by any fixed integer
\(\widehat C>2^{8838}\) for which (T.mix) holds with
\[
 \widehat\epsilon_m=\min\{2,\widehat C m^{-2314/25}\}.
                                                        \tag{B.coefficientscope}
\]
Indeed this supplies both the order-92 and order-six estimates,
and \(S_{92}<2^{8838}<\widehat C\) supplies the coefficient in (B.onerate). The remaining
bounds are the same scalar inequalities. With
\(\widehat F_b=2^{467}b16^b(\widehat C+1)\), the survival theorem
in the next section is unchanged, its variation tail still tends to
zero, and its finite startup and root-pool recipes give a positive
score. The startup inequalities use \(t=\lceil\log_2\widehat F_b\rceil
\ge4b\), which is retained.

The sufficient condition \(\widehat C>2^{8838}\) is used through
\(S_{92}<\widehat C\) in (B.onerate). The startup bound
\(t\ge4b=2^{27}>25637\) holds for every \(\widehat C\ge1\).
Thus the finite startup argument applies throughout this coefficient range;
the explicit construction takes \(\widehat C=C_6\).

## 8. Infinite survival and a fixed persistent root score {#chapter08}

The preceding section bounded the total future variation of the seed marks.
We now show that their reference average stays above that loss after a
fixed initial stage. A complete finite period of known convergent roots
realizes the reference average. Allocating the remaining mass among these
roots gives a positive lower bound for their reciprocal-root weighted sum,
called the *root score*. This establishes (G.marks), the premise needed by
the finite continuation and terminal-source constructions. The survival
estimate below uses a summable fixed-time tail and small rational inequalities.

### A short proof of reference survival

Fix \(b=32^5=2^{25}\), retaining the fixed-depth stage families,
success masses \(p_j\), floors \(b_j\) and marks of Section 7.
Put
\[
 \alpha=\frac{100999}{100000},\qquad r=\frac{504}{503},\qquad
 u=\frac{511}{64},\qquad d_j=2e^{-ur^j}.              \tag{R.deficits}
\]
The recurrence gives \(b_j\ge b\alpha^j\), and the exact comparisons
\[
 100999\,503^5-100000\,504^5=32325056940257>0,\qquad
 \frac{32}{4+3/512}=\frac{16384}{2051}>\frac{511}{64}
                                                               \tag{R.survivalguards}
\]
show that (B.failure) implies \(0\le1-p_j\le d_j\).

The function \(f(t)=e^{-ur^t}\) is decreasing on \([0,\infty)\).
Thus \(\sum_{j\ge0}f(j)\le f(0)+\int_0^\infty f(t)\,dt\).
Substitution \(x=ur^t\), followed by
\(\log r>1/504\), gives
\[
 \sum_{j\ge0}d_j
 <2e^{-u}\left[
  1+504\left(\frac1u-\frac1{u^2}+\frac2{u^3}\right)\right].
                                                               \tag{R.survivalsum}
\]
Here \(\log(1+x)>x/(1+x)\) for \(x>0\) follows by integration
of \(1/(1+t)\). For the integral estimate used in (R.survivalsum),
write
\[
 \int_u^\infty\frac{e^{-x}}x\,dx
 =e^{-u}\int_0^\infty\frac{e^{-t}}{u+t}\,dt
 \le e^{-u}\left(\frac1u-\frac1{u^2}+\frac2{u^3}\right).
\]
The pointwise inequality
\(1/(u+t)\le1/u-t/u^2+t^2/u^3\) holds for \(t\ge0\);
multiplication by \(u+t\) leaves the nonnegative remainder \(t^3/u^3\).
Integrating \(1,t,t^2\) against \(e^{-t}\) gives \(1,1,2\).

The required numerical comparisons are:
\[
 \frac1u-\frac1{u^2}+\frac2{u^3}
 =\frac{15142976}{133432831}<\frac{227}{2000},
 \qquad e^u>2920.                                   \tag{R.exponentialguard}
\]
For the second use \(u=8-1/64\),
\[
 e^8>\sum_{k=0}^{16}\frac{8^k}{k!}
   =\frac{70233453593}{23648625},\qquad
 e^{-1/64}>63/64,
\]
and
\[
 63\cdot70233453593
 -2920\cdot64\cdot23648625=5252536359>0.
\]
Consequently
\[
 \sum_{j\ge0}(1-p_j)
 <\frac2{2920}\left(1+504\frac{227}{2000}\right)
 =\frac{14551}{365000}<\frac1{25}.                   \tag{R.failurebudget}
\]
For a finite product,
\(\prod_{j<N}p_j\ge1-\sum_{j<N}(1-p_j)\), by induction from
\((1-a)(1-b)\ge1-a-b\) for \(0\le a,b\le1\).
The finite products decrease in \([0,1]\), so their limit exists.
We have therefore proved
\[
 \boxed{\Pi=\frac{24}{25},\qquad
 \prod_{j<N}p_j>\Pi\ (N\ge0),\qquad
 \prod_{j\ge0}p_j\ge\Pi.}                            \tag{R.certificate}
\]
This proves survival from the displayed rational inequalities. The finite
reference-moment tables are separate inputs to the quantitative density formula.

### Complete variation tail and earliest positive startup

For the canonical score use \(C_6\) from
[the reference-mixing section](#chapter06). The qualitative alternative
(B.coefficientscope) may replace it throughout this section by
\(\widehat C\), retaining both the order-92 estimate and its scalar
size condition. A coefficient supplying only order six does not suffice.
Define

\[
 F_b=2^{467}b16^b(C_6+1),\quad
 t=\lceil\log_2F_b\rceil,\quad L=\lceil\log_2(t+1)\rceil,
\]
\[
 a=2013\,100000^{92},\quad d=2000\,100999^{92},\quad
 \lambda=a/d,\quad
 V(n)=2^tT_3(n,\lambda),\quad
 T_3(n,z)=\sum_{j\ge n}(j+1)^3z^j.                    \tag{R.variationdata}
\]

Thus \(t\) is an integer, \(F_b\le2^t\), \(t\ge4b=2^{27}\), and
\(t<2^L\). The canonical arithmetic specification of \(C_6\) makes
\(t\) an effective integer; it is not necessary to print its expansion.
By (B.tail), for every admissible root \(M\) and every \(j\ge n\),

\[
 |Z_j(M)-Z_n(M)|\le V(n).                             \tag{R.latermarks}
\]

For \(0<z<1\), expanding \((n+1+h)^3\) and summing the four absolutely
convergent geometric moment series gives

\[
 T_3(n,z)=z^n\left[
 \frac{(n+1)^3}{1-z}+
 \frac{3(n+1)^2z}{(1-z)^2}+
 \frac{3(n+1)z(1+z)}{(1-z)^3}+
 \frac{z(1+4z+z^2)}{(1-z)^4}\right].                  \tag{R.exacttail}
\]

The geometric moments follow by differentiating \(\sum_{h\ge0}z^h\)
on any compact subinterval of \((0,1)\), or directly by multiplying
their convergent sums by \(1-z\). Hence this is an exact rational
function at \(z=\lambda\). Also
\(V(n)-V(n+1)=2^t(n+1)^3\lambda^n>0\).

The rational inequalities (B.ratebounds) give \(2/5<\lambda<41/100\).
The additional finite integer comparison is

\[
 2^{131}2013^{100}100000^{9200}
       <2000^{100}100999^{9200},\qquad
 \lambda^{100}<2^{-131}.                             \tag{R.hundredrate}
\]

If \(n\ge16\) and \(0<z\le41/100\), successive terms of \(T_3(n,z)\)
have ratio at most
\((41/100)(18/17)^3<1/2\); the last inequality is
\(478224<491300\). Therefore

\[
 T_3(n,z)<2(n+1)^3z^n.                               \tag{R.tailmajorant}
\]

For the fixed-budget comparison and a finite upper bound on the startup, put
\(N_{\rm fixed}=\lceil100(t+3L+214)/131\rceil\). For all integers
\(t\ge25637\),

\[
 17\le N_{\rm fixed}\le(100t+300L+21530)/131\le4t/5.         \tag{R.searchguard}
\]

For the upper bound write \(k=\lfloor\log_2t\rfloor\ge14\), so
\(L=k+1\). It suffices that
\(1500(k+1)+107650\le24\,2^k\). At \(k=14\) this is
\(130150\le393216\); its right increment exceeds its left increment
1500 for every later \(k\). The ceiling bound and the elementary lower
bound on \(N_{\rm fixed}\) give the other claims.

The hundred-step comparison applies to every integer exponent:
\((\lambda^n)^{100}<2^{-131n}\) for \(n\ge1\). No divisibility
condition on \(n\) is present. Since \(\lambda^{-1}<5/2\),
(R.searchguard) and (R.tailmajorant) imply

\[
 \begin{split}
 V(N_{\rm fixed}-1)
 &<2^{t+1}N_{\rm fixed}^3\lambda^{N_{\rm fixed}-1}\\
 &<2(4/5)^3(5/2)\,2^{t+3L-131N_{\rm fixed}/100}\\
 &\le(64/25)2^{-214}<3\,2^{-214}<\Pi.
 \end{split}                                         \tag{R.searchendpoint}
\]

Consequently the exact definitions

\[
 N=\min\{n\ge16:V(n)<\Pi\},\qquad
 P=\Pi-V(N)>0                                       \tag{R.residual}
\]

make sense, with \(16\le N\le N_{\rm fixed}-1\). Strict monotonicity of
\(V\) permits rational binary search on this finite interval. All
values below 16 fail the positivity predicate: the tail then contains
\(17^3\lambda^{16}>17^3 2^{-32}\), and multiplication by \(2^t\)
already exceeds one. This defines the startup by a finite integer recipe. The exact
value \(\Pi=24/25\), and then the whole residual \(P\), are retained.

For later quantitative comparisons one needs more than \(P>0\).
Let \(e=d-a>0\), and for any integer \(n\ge0\) define

\[
 U_n=d\big[(n+1)^3e^3+3(n+1)^2ae^2+
           3(n+1)a(d+a)e+a(d^2+4ad+a^2)\big].
\]

Substitution into (R.exacttail) gives
\(T_3(n,\lambda)=a^nU_n/[d^n(d-a)^4]\). If
\(P(n)=\Pi-V(n)>0\), its numerator over the common denominator
\(25d^n(d-a)^4\) is a positive integer. Because
\(d<2^{11+17\cdot92}=2^{1575}\),

\[
 P(n)\ge[25d^n(d-a)^4]^{-1}
                  >2^{-1575n-6305}>2^{-1575n-7324}.                  \tag{R.denominator}
\]

Here \(25<2^5\); the final weaker bound is retained for the startup comparison.
No reduced-denominator calculation or lower bound on the numerical
distance to a threshold is assumed. The integer \(2^t\) adds no denominator.

### The fixed finite convergent root pool

Write \(q=q_N\) as in (B.conductor), and let

\[
 H=2b+1,\quad
 \mathcal S_q=\{s\in\mathbb Z:H\le s<H+3^q,\ 3\nmid s\},
 \quad R_s=(4^s-1)/3,\quad K_q=2\,3^{q-1},\quad
 B_q=(2/3)2^q.                                      \tag{R.pool}
\]

Here \(q\ge\lfloor b/4\rfloor=2^{23}\). [The reference-transfer section](#chapter02)'s root-period
lemma proves that \(s\mapsto R_s\bmod3^q\) is a bijection from
\(\mathcal S_q\) onto the unit residues. Thus this is a finite pool of
exactly \(K_q\) distinct roots. Each is odd and
\(R_s\ge R_H=(4\,16^b-1)/3>16^b>1\). Moreover
\(3R_s+1=4^s\), so its next accelerated odd iterate is one, and its
ordinary stopping time is \(1+2s\). The root pool and its maximum clock
are finite and fixed before any physical counting cutoff.

Set \(g_s=g_N(R_s\bmod3^q)\). By (B.mean), (B.cap), (B.physical),
and the reference survival bound,

\[
 0\le g_s\le B_q,\quad Z_N(R_s)=g_s,\quad
 \sum_{s\in\mathcal S_q}g_s
       =K_q\prod_{j<N}p_j\ge K_q\Pi.                 \tag{R.rootmean}
\]

The unit-relative mean on the right is \(\prod p_j\), not
\((2/3)\prod p_j\). The latter is the full-group mean before restricting
to unit support. This step is an exact finite period, not equidistribution
of actual sources.

Define the persistent lower marks by

\[
 z_s=(g_s-V(N))_+.
\]

They satisfy \(0\le z_s\le B_q\), and since \((x-y)_+\ge x-y\),

\[
 \sum_s z_s\ge K_qP,\qquad
 Z_j(R_s)\ge z_s\quad(j\ge N,\ s\in\mathcal S_q).     \tag{R.persistence}
\]

For the second claim use (R.latermarks) and \(Z_j\ge0\). The bound
includes the entire future variation tail. No assumption that every root survives is made.

### Exact weighted allocation and discharge of the graft input

For \(q\ge1\) and \(0\le p\le1\), define

\[
 W(q,p)=\min\left\{\sum_{s\in\mathcal S_q}\frac{v_s}{R_s}:
       0\le v_s\le B_q,\quad \sum_s v_s\ge K_qp\right\},
 \qquad W_*=W(q_N,P).                             \tag{R.score}
\]

The fixed constant \(W_*\) names the score for the chosen construction:
\(N\) is the earliest stage with positive guaranteed residual, and the
full residual \(P=\Pi-V(N)\) is retained. The minimum accounts for the
least favorable allocation of that residual among the specified roots.

The constant \(H\) remains fixed. The feasible region is nonempty
(take \(v_s=p\), since \(B_q\ge4/3\)), compact, and finite dimensional.
The objective is continuous, so the minimum exists. Its coefficients
are strictly positive; a minimizer has total mass exactly \(K_qp\),
by decreasing some coordinate if necessary. For \(p>0\),
\(W(q,p)\ge K_qp/\max_s R_s>0\).

For the following evaluation only, relabel the roots in decreasing order
as \(R_1>\cdots>R_{K_q}\).
Write \(h=\lfloor K_qp/B_q\rfloor\), \(r_0=K_qp-hB_q\). Since
\(p\le1<B_q\), \(h<K_q\). Then

\[
 W(q,p)=B_q\sum_{i=1}^{h}R_i^{-1}+r_0R_{h+1}^{-1}.    \tag{R.greedy}
\]

Indeed, if a smaller root has positive mass and a larger root has spare
capacity, moving the minimum of those two amounts to the larger root
strictly decreases the objective. Repeating this exchange proves the
displayed formula, including zero mass, exact cap boundaries, and one
partial cap. At fixed \(q\), \(W(q,p)\) is continuous and strictly
increasing in \(p\): between cap boundaries its slope is one of the
positive numbers \(K_q/R_i\).

For later comparisons, decreasing the level also has a precise
effect on the minimum. At fixed \(H\), \(q\ge2\) and \(0<p\le1\),
\[
 W(q+1,p)<3\,4^{-(3^q+1)}W(q,p).                    \tag{R.conductormonotone}
\]
Indeed, allocate mass \(3p\) to each unit index in the last interval
\([H+2\cdot3^q,H+3^{q+1})\) of \(\mathcal S_{q+1}\).
It contains exactly \(K_q\) such indices; the allocation is feasible,
since \(B_{q+1}\ge3\) and \(3K_q=K_{q+1}\).
Its smallest root exceeds \(4^{3^q+1}\) times the largest root
in \(\mathcal S_q\): the index gap is at least \(3^q+1\), and
\(R_{s+\Delta}>4^\Delta R_s\). Compare this feasible upper bound with
\(W(q,p)\ge K_qp/\max_{\mathcal S_q}R_s\).
Iterating gives, for \(Q>q\ge2\),
\[
 W(q,p)>
 (4/3)^{Q-q}2^{\,3^Q-3^q}W(Q,p).                    \tag{R.conductorgain}
\]
This comparison uses the exact cap and minimum-allocation definition,
rather than assuming that a smaller root pool automatically helps.

By (R.persistence), the actual lower vector \((z_s)\) is feasible in
(R.score). Thus

\[
 0<W_*\le\sum_{s\in\mathcal S_q}\frac{z_s}{R_s},
 \qquad Z_j(R_s)\ge z_s\quad(j\ge N).                 \tag{R.graftinput}
\]

This is precisely (G.marks), with one fixed finite root pool, one fixed
startup, and the same explicit score \(W_*\). The score is a lower
certificate obtained by minimum allocation; it is not the unknown actual
weighted sum of the marks and need not equal that sum.

The fixed-pool graft theorem (G.pool) supplies the input to (N.sourcefamily)
with ordinary clock \((10431/1000)\log x\). Its parameterized version
(N.paramgraft)--(N.everyclock) supplies, for every fixed \(c>c_0\),
the same score, aggregate source-weight bound and coverage at every large
real scale with clock
\(c\log x\). The order is: canonical constants, certificate, startup,
pool and score; then \(c\), a positive terminal ratio, a positive graft
tolerance and one finite splice; finally every sufficiently large cutoff. No root or seed precision is selected
afresh as a function of that cutoff. The terminal stage and level may
vary along the fixed graft schedule, as in (N.sourcefamily).

### General residue-complete blocks and their common score

Let \(\mathcal F\) be a nonempty finite collection of disjoint root blocks.
Fix \(q\ge2\). Each block has one odd root \(M_i(r)\ge16^b\) in every unit residue
\(r\bmod3^q\). Put
\[
 \mathcal U_q=(\mathbb Z/3^q\mathbb Z)^\times,\qquad
 A_{\mathcal F}(r)=\sum_i\frac1{M_i(r)},\qquad
 \mathcal V(q,p)=\{v:0\le v_r\le B_q,\ \sum_rv_r\ge K_qp\},
\]
\[
 W_{\mathcal F}^{\rm joint}(q,p)
   =\min_{v\in\mathcal V(q,p)}\sum_rv_rA_{\mathcal F}(r),\qquad
 W_i(q,p)=\min_{v\in\mathcal V(q,p)}\sum_r\frac{v_r}{M_i(r)}.
                                                        \tag{R.jointscore}
\]
Here \(0<p\le1\); at \(p=0\) every score is zero. Each minimum exists,
is positive and is rational for rational \(p\).

For the persistent-mark application, specialize to the selected startup
\(N\) and put
\[
 \boxed{q=q_N,\qquad p=P.}                            \tag{R.markapplication}
\]
Retain the corresponding \(B_q,K_q\). Then
\(z_r=(g_N(r)-V(N))_+\) is feasible by the mean, capacity and full
variation bounds (B.mean), (B.cap) and (R.latermarks), as in (R.persistence).
Thus the joint score is an available persistent score whenever the union
has the required counting and target-path properties.
The finite allocation statements below remain valid for every \(q\ge2\)
and \(0\le p\le1\).

**Proposition (shared allocation and coverage).**
\[
 W_{\mathcal F}^{\rm joint}(q,p)\ge\sum_iW_i(q,p),
                                                        \tag{R.jointdominance}
\]
with equality exactly when all block objectives have a common minimizing
residue allocation. In particular
\[
 \min_r A_{\mathcal F}(r)\ge a_{\mathcal F}
 \quad\Longrightarrow\quad
 W_{\mathcal F}^{\rm joint}(q,p)\ge K_qp\,a_{\mathcal F}.
                                                        \tag{R.coverage}
\]

*Proof.* The feasible set is nonempty and compact. Since every cost is
positive, a minimizer uses total mass exactly \(K_qp\). The exchange
argument of (R.greedy) fills the smallest costs first and proves rationality.
All blocks use one common residue vector.
For every feasible vector each summand is at least its separate minimum;
equality in their sum requires equality in every summand. The coverage
bound follows by multiplying its coefficient bound by the total mass.
\(\square\)

**Lemma (affine block comparison).** Suppose a block uses the baseline indices
\(\mathcal S_q\), is residue-complete, and has
\[
 M_s=\alpha R_s+\frac{\alpha-1}{3},\quad0<\alpha<1.
 \qquad
 W_M(q,p)>\alpha^{-1}W(q,p)\quad(p>0).                \tag{R.blockcomparison}
\]
Indeed \(M_s<\alpha R_s\) pointwise. Evaluate the strict reciprocal
inequality at a minimizer for this block; at least one coordinate
has positive mass. The baseline-root objective of that vector is at least
\(W(q,p)\). This argument uses the common cap and total mass and does
not assume invariance of \(g_N\) under the residue permutation.
A proved upper coefficient \(\alpha\le\beta<1\) gives the weaker factor
\(\beta^{-1}\). These finite comparisons will be used in Appendix C.

### Quantitative score bounds and the fixed-recipe optimum

For \(p>0\), every root in \(\mathcal S_q\) is less than
\(4^{H+3^q}/12\). Hence the required total mass gives

\[
 W(q,p)>8p\,3^q4^{-(H+3^q)}.                         \tag{R.scorelower}
\]

For \(q\ge3\) and \(0<p\le1\), the upper half-period of indices
\(H+(3^q+1)/2\le s<H+3^q\) contains at least
\(3^{q-1}-1\) indices not divisible by three. This follows either by
counting residues modulo three in that interval or by deleting at most
one excess multiple of three from its two-thirds proportion. Its total
capacity is at least
\((3^{q-1}-1)(2/3)2^q\ge2\,3^{q-1}=K_q\):
\((1-3^{1-q})2^q\ge3\) already holds at three and increases.
Every root there exceeds \(2^{3^q}\), because \(H\ge1\) and
\(2s\ge2H+3^q+1\). A feasible allocation supported there proves

\[
 W(q,p)\le3^q2^{-3^q}.                               \tag{R.scoreupper}
\]

For \(p=0\) this bound follows from \(W(q,0)=0\). The bound concerns
the minimum, not every feasible vector. The right side decreases for
integer \(q\ge1\), as its successive ratio is \(3\,2^{-2\cdot3^q}<1\).
At the actual \(q\ge2^{23}>18\), use \(3^q<2^{2q}\) and
\(3^{18}-36=387420453\) to obtain

\[
 0<W_*<2^{-134217727}<2^{-4096}.                   \tag{R.scoredomain}
\]

This supplies the small-score domain of the fractional-moment density
comparison without evaluating the score or using an empirical estimate.

It is also useful to retain why this particular startup is optimal within
the fixed certificate and rounded one-rate majorant. For the level
\(q(n)=q_n\),

\[
 q(n)\ge bn,\qquad H\le8q(n)+7,\qquad
 q(n+1)\ge q(n)+1.                                  \tag{R.conductorguards}
\]

The first follows by retaining \(b_j\ge b\) in its sum, the second from
\(q(n)\ge\lfloor b/4\rfloor\), and the third from the new positive
summand and nondecreasing terminal quarter. Fix any later \(n>N\) and
any \(0<p\le1\), and put \(q=q_N\). By (R.scoreupper) and its
monotonicity, the later score is at most \(3^{q+1}2^{-3^{q+1}}\).
Combining (R.scorelower), (R.denominator) at \(N\), and
(R.conductorguards), gives

\[
 \begin{split}
 \log_2\frac{W_*}{W(q(n),p)}
 &>3^q-2H+3-\log_2 3-1575N-7324\\
 &>3^q-17q-7337\ge12193.
 \end{split}                                         \tag{R.startupoptimum}
\]

Here \(1575N\le q\) since \(b>1575\). The last function equals
12193 at \(q=9\) and has positive successive increments
\(2\,3^q-17\); all actual levels exceed nine.
Earlier startups leave no positive guaranteed budget under this same
majorant. At \(N\), (R.residual) is the largest budget it allows, and
fixed-level score monotonicity shows that no smaller budget improves
the score. Every later startup loses even if allowed budget one. Thus
the selected startup and its full residual uniquely optimize this
minimum-score recipe. This does not optimize the underlying variation
coefficient, reference family, actual marks, or alternative root pools.
The rational residual condition and large-level condition are essential:
an arbitrary tiny real budget in an earlier small pool need not beat a
later pool.

The coefficient dependence of the startup, residual, and root score is
proved in [Appendix B](#appendix_provenance).

### The score used in counting

The fixed-depth survival proof, complete variation bound and earliest
positive allocation provide the score used below. They use the affine
transfer, root-period, capacity and finite-graft estimates proved in the
preceding sections. Appendix A compares this score with the
central first-crossing benchmark.

The reproducibility archive contains the rational survival and rate checks.
The all-stage estimates use the primitive coefficient (M.canonicalC);
(B.coefficientscope) gives the variant with a general mixing coefficient.
We next estimate the reference moments used to convert the score into an
ordinary counting bound.

## 9. Reference moments and their finite certificates {#chapter09}

We now bound the concentration of the reference fan by its maximum,
variance, and average power of order \(3/2\). The counting section will
use these three bounds to turn a guaranteed marked sum into a lower bound
on total source weight. All moments concern the auxiliary law (T.law).
A product inequality propagates finite moment bounds to every level, so
finite certificates suffice for the estimates used at arbitrarily large
moduli.

### Orientation and a conditional affine mixture

Let \(T_a(x)=(3x+1)/2^a\), interpreted in the appropriate ternary ring.
The composition \(T_{a_n}\cdots T_{a_1}(0)\) is
\[
 \sum_{i=1}^n3^{n-i}2^{-(a_i+\cdots+a_n)}.
\]
Reversing a finite iid word turns this into the offset sum in (T.law),
without changing its probability \(2^{-\sum a_i}\). Thus the forward
random affine construction and the inverse-prefix construction have the
same law at every level. The physical histories retain the orientation fixed in (W.inverse).

For \(p\ge1\) put
\[
 M_p(n)=\langle f_n^p\rangle_n,\qquad A_n=\max_{G_n}f_n.
                                                        \tag{F.norms}
\]
All averages in this section are over the full group, including zero and
the nonunits. We have \(M_1(n)=1\), \(M_p(0)=A_0=1\).

**Theorem (moment inheritance).** For integers \(u,v\ge0\) and real
\(p\ge1\),
\[
 M_p(u+v)\le M_p(u)M_p(v),\qquad A_{u+v}\le A_uA_v.
                                                        \tag{F.inheritance}
\]

*Proof.* Zero-length blocks give equality. Otherwise condition on the last
\(v\) forward valuations, a word \(w\) with probability \(\theta_w\).
Its affine action is \(b_w+3^vc_wx\), where \(c_w\) is a ternary unit.
For \(y\in G_v\), write the lifts as \(y+3^vz\), \(z\in G_u\).
For each word with \(b_w\equiv y\pmod{3^v}\), the equation for the final
residue determines the preceding residue as an affine permutation
\(x=\psi_w(z)\) of \(G_u\). Independence of the two reference blocks
gives the exact identity
\[
 f_{u+v}(y+3^vz)=3^v
   \sum_{w:b_w\equiv y\ (3^v)}\theta_w f_u(\psi_w(z)).
                                                        \tag{F.mixture}
\]
The nonnegative coefficients sum to \(f_v(y)\). If this sum vanishes,
the whole fiber vanishes. Otherwise divide by it and apply Jensen's
inequality to the probability mixture. Every \(\psi_w\) preserves the
full average, so averaging first over \(z\) and then over \(y\) gives
the first assertion. Bounding each \(f_u\) by \(A_u\) instead gives
\(f_{u+v}(y+3^vz)\le A_uf_v(y)\), proving the second. Countably many
words cause no problem: the functions on each finite group are bounded,
and the coefficients have finite sum; Jensen follows by truncation and
one remainder atom, or directly for a countable probability distribution.
\(\square\)

For a probability law on a finite group, its collision probability is the
sum of the squared point probabilities: this is the chance that two
independent samples agree. In particular the normalized collision energy is
\(M_2(n)=3^n\sum_y\mu_n(y)^2\), and is submultiplicative. General
\(p\) matters: interpolation between the maximum and this second moment
does not supply the smaller direct \(p=3/2\) table below.

The general convex-order inequality and the divergence consequences of
moment inheritance are collected in [Appendix D](#appendix_reference_consequences). The
moment inequality above is all that is needed for the finite certificates
and their propagation below.

### The whole affine fan and the exact coset split

Conditioning on the last forward valuation gives
\[
 f_{n+1}(y)=3\sum_{\substack{a\ge1\\2^ay\equiv1\ (3)}}
 2^{-a}f_n\left((2^ay-1)/3\bmod3^n\right).
                                                        \tag{F.transfer}
\]
The divisibility condition and the modulus \(3^{n+1}\) on \(y\)
make the argument well defined. Define
\[
 F_j(x)=4^jx+(4^j-1)/3,\qquad
 H_m(x)=\sum_{j\ge0}4^{-j}\rho_m(F_j(x)),\qquad
 \phi_m(x)=(3x+1)/2\pmod{3^{m+1}}.
                                                        \tag{F.fan}
\]
Every \(F_j\) permutes \(G_m\); the series converges absolutely.
The map \(\phi_m:G_m\to G_{m+1}\) is a bijection onto the
\(2\pmod3\) coset: equality of its values is equivalent to equality
of its inputs modulo \(3^m\). At its image the allowed exponents in
(F.transfer) are \(a=2j+1\), with predecessor \(F_j(x)\). Therefore
\[
 H_m(x)=\frac49f_{m+1}(\phi_m(x)).                     \tag{F.fanidentity}
\]
If \(y\equiv1\pmod3\), shifting its even admissible exponents down
by one proves \(f_{n}(2y)=2f_n(y)\) for \(n\ge1\).
The nonunit coset is zero. Since multiplication by two bijects the two
unit cosets, the \(p\)-power sums on them have ratio \(1:2^p\).
Consequently
\[
 \langle H_m^p\rangle_m=
       \frac{3(8/9)^p}{1+2^p}M_p(m+1),\qquad
 \langle H_m\rangle_m=\frac89=:\mu,
 \quad \langle H_m^2\rangle_m=\frac{64}{135}M_2(m+1).
                                                        \tag{F.fanmoments}
\]
These constants use full-group averages, not unit-relative ones. The
maximum likewise lies in the \(2\)-coset, since every value on the
\(1\)-coset is doubled on its image. Thus
\[
 \|H_m\|_\infty=\frac49 A_{m+1}.                      \tag{F.fanmax}
\]

The word with all \(m+1\) valuations equal to one has probability
\(2^{-(m+1)}\) and endpoint \(-1\pmod{3^{m+1}}\). Since
\(\phi_m(-1)=-1\), it also proves the coherent lower bound
\[
 H_m(-1)\ge\frac23(3/2)^m.                            \tag{F.spike}
\]
This all-depth family rules out a polynomial fan maximum. It does not
rule out a polynomial collision or fractional moment, because its
support occupies a decreasing fraction of the residue group.

### The finite inequalities used by the density recipe

The finite certificate consists precisely of
\[
 A_d\le a_d\quad(0\le d\le16),\qquad
 M_2(d)\le e_d\quad(0\le d\le16),\qquad
 M_{3/2}(d)\le b_d\quad(0\le d\le16),                 \tag{F.finitetarget}
\]
with the following rational values. The first three maximum and collision
values are exact; the subsequent comparisons may be proved strictly.

| \(d\) | \(a_d\) | \(e_d\) | \(b_d\) |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 |
| 1 | 2 | 5/3 | 1276143/1000000 |
| 2 | 22/7 | 15/7 | 711317/500000 |
| 3 | 24/5 | 521/200 | 769803/500000 |
| 4 | 73/10 | 3069/1000 | 32779/20000 |
| 5 | 11 | 707/200 | 862279/500000 |
| 6 | 17 | 4001/1000 | 449901/250000 |
| 7 | 25 | 2233/500 | 116627/62500 |
| 8 | 38 | 1233/250 | 962777/500000 |
| 9 | 57 | 5399/1000 | 1979303/1000000 |
| 10 | 85 | 2933/500 | 253519/125000 |
| 11 | 127 | 3167/500 | 259093/125000 |
| 12 | 948/5 | 6803/1000 | 422721/200000 |
| 13 | 1896/5 | 7273/1000 | 134447/62500 |
| 14 | 20856/35 | 7743/1000 | 109287/50000 |
| 15 | 3201/5 | 4107/500 | 2217669/1000000 |
| 16 | 4802/5 | 1737/200 | 561799/250000 |

The horizons fix the finite work needed by this recipe. Depth sixteen
supplies the retained second-moment block rate \(e_{16}^{1/16}\);
depth twelve supplies the direct fractional rate \(b_{12}^{1/6}\)
and the rational inequality \(b_{12}^2<(57/50)^{12}\), together
with its remainder bounds. The latter rate is smaller, so the comparison
compensates for the fractional branch's extra residual-mass power.
The quantitative comparison (Q.paid) checks this on its stated small-score range.
These are sufficient certificate choices, not minimal depths for a
rate advantage: already \(b_{11}^{32}<e_{16}^{11}\).
The twelve-step fractional formula is retained as a named benchmark.
The sixteen-step certificate gives the smaller propagated denominator rate
\[
 b_{16}^{1/8}=1.10650942918\ldots
 <b_{12}^{1/6}=1.13284538025\ldots .                  \tag{F.sixteenrate}
\]
These are rates of certified ceilings, not assertions about the true
asymptotic moments. Section 11 compares the complete optimized formulas.

Here is a complete specification of the finite verification and why it is
an upper-bound certificate. Let \(S=2^t\), and suppose the nonnegative
integer array \(z\) bounds \(Sf_{d-1}\) entrywise. Positivity of
(F.transfer) allows its input to be replaced by \(z\). All divisions
below round upward.

In the cyclic algorithm the powers of two enumerate the units modulo
\(3^d\) in a cycle of length \(\ell=2\cdot3^{d-1}\). Indeed, the
valuation formula proved for (T.law)'s root period gives order
\(3^{d-1}\) for four and hence order \(2\cdot3^{d-1}\) for two.
Write \(y_i=2^i\bmod3^d\), and put
\(g(i)=z_{(y_i-1)/3}\) on the \(1\)-coset and zero otherwise.
The infinite sum
\[
 h(i)=\sum_{a\ge1}2^{-a}g(i+a)
      =\tfrac12(g(i+1)+h(i+1))                        \tag{F.cyclic}
\]
is periodic. Its first \(T\) terms at zero plus
\((\max z)2^{-T}\) bound \(h(0)\). Starting with that upward-rounded
bound, iterate (F.cyclic) backwards at \(i=\ell-1,\ldots,1\).
Induction gives an upper bound at every index; no approximate fixed-point
solve is used. Assign \(3h(i)\) to the unit \(y_i\), and zero to
the nonunits. The code checks the whole cycle and uniqueness explicitly.

The separate direct algorithm evaluates every unit independently. Let
\(e=1\) on the \(2\)-coset and \(e=2\) on the \(1\)-coset, and
\(x_0=(2^ey-1)/3\bmod3^{d-1}\), \(x_{j+1}=4x_j+1\).
For \(J\) terms put \(A=\sum_{j=0}^{J-1}4^{J-1-j}z_{x_j}\).
The exact positive infinite parity sum is bounded by
\[
 \frac{3A+\max z}{2^{e+2J-2}}.                       \tag{F.direct}
\]
To verify the tail, multiply \(3\cdot2^{-e}\sum_{j\ge J}4^{-j}
\max z\) by the displayed denominator; the product is exactly
\(\max z\). This proves both tail and normalization before rounding.

For the depth-sixteen maximum and collision table, use \(t=48\),
\(T=96\), \(J=16\), seeding both algorithms with upward rounding
of the exact depth-two vector
\[
 f_2=(0,8/7,16/7,0,11/7,4/7,0,2/7,22/7).             \tag{F.exacttwo}
\]
Compute \(\max z/S\) and \(\sum z_y^2/(3^dS^2)\) at every
depth through sixteen. Checked unsigned 64-bit arrays store the entries;
all transfer, energy and comparison arithmetic uses unbounded integers.
Every array assignment rejects overflow. The largest group has
\(3^{16}=43{,}046{,}721\) entries; no residue class is sampled.

For the fractional rows through twelve, both algorithms also run with
\(t=128\), \(T=168\), \(J=32\), starting from \(f_0=1\).
For any even \(t\) and upper vector \(z\ge2^tf_d\),
\[
 M_{3/2}(d)\le
 \frac{\sum_y z_y\lceil\sqrt{z_y}\rceil}{3^d2^{3t/2}}.
                                                        \tag{F.sqrtcertificate}
\]
The ceiling square root is found by integer square root and a perfect-square
test. Thus no floating approximation of a fractional power decides a table
inequality. Positive partial sums rounded downward supply independent lower controls.
The cyclic \(t=48\), \(T=96\) arrays give the additional fractional
rows through sixteen by the same inequality, now with denominator
\(3^d2^{72}\). The final full-group computation gives
\[
 M_{3/2}(16)\le
 \frac{456815260910074290115278246270}
      {203282392447840896882957090816}
 <\frac{561799}{250000}=2.247196.                    \tag{F.sixteencertificate}
\]
The denominator is exactly \(3^{16}2^{72}\). This calculation uses
all \(43{,}046{,}721\) residues, checked unsigned 64-bit storage, and
unbounded integers for arithmetic and the square-root sum. It requires
no second full direct fractional run through sixteen.

As a calibration, an exact rational parity sum through a full period
\(3^{d-1}\) computes every entry through depth five; its denominator
contains \(4^{3^{d-1}}-1\). It checks (F.exacttwo), full means, coset
ratios, projection and the fan identities against both upper algorithms.
The implementations and complete certificate records are supplied in the
[reproducibility archive](#formalization_data). The product inequality
(F.inheritance) extends the finite table bounds to all levels.

### All-level moment bounds

For \(n=16s+r\), \(0\le r<16\), and separately \(n=12t+j\),
\(0\le j<12\), define
\[
 D_n=e_{16}^{s}e_r,\qquad D_n^{(3/2)}=b_{12}^{t}b_j.
                                                        \tag{F.blockceilings}
\]
Also define a finite dynamic minimum recursively by
\[
 \widehat A_0=1,\qquad
 \widehat A_n=\min_{1\le j\le\min(n,16)}a_j\widehat A_{n-j}.
                                                        \tag{F.dynamic}
\]
The inheritance theorem and induction prove
\(M_2(n)\le D_n\), \(M_{3/2}(n)\le D_n^{(3/2)}\), and
\(A_n\le\widehat A_n\). Each term in the minimum is a valid upper
bound; minimizing never relies on mutually compatible extremizers.

Put \(\beta_s=31/20\), \(\beta_f=57/50\). Exact rational comparisons
of the finite table give
\[
 a_{12}<\beta_s^{12},\quad
 a_r\le2\beta_s^{r-1}\ (0\le r<12,\ r\ne2),\quad
 a_{12}a_2<2\beta_s^{13},                             \tag{F.supgates}
\]
\[
 b_{12}^2<\beta_f^{12},\qquad b_r^2\le4\beta_f^r
       \ (0\le r<12).                               \tag{F.fracgates}
\]
For \(n=m+1\ge3\), write \(n=12s+r\). Unless \(r=2\),
(F.supgates) gives \(A_n\le2\beta_s^{n-1}\). In the exceptional
case \(s\ge1\); use \(a_{12}^{s-1}(a_{12}a_2)\) instead.
Consequently the following ceilings are valid for every \(m\ge2\):
\[
 \begin{aligned}
 S_m&=\min\{(8/9)\beta_s^m,(4/9)\widehat A_{m+1}\},
       &\|H_m\|_\infty&\le S_m,\\
 V_m&=(64/135)D_{m+1}-\mu^2,
       &\langle(H_m-\mu)^2\rangle_m&\le V_m,\\
 \mathcal B_m&=\frac{3(8/9)^{3/2}}{1+2^{3/2}}D_{m+1}^{(3/2)},
       &\langle H_m^{3/2}\rangle_m&\le\mathcal B_m.
 \end{aligned}                                        \tag{F.ceilings}
\]
The variance ceiling is positive: \(D_n\ge521/200>5/3\) for
\(3\le n<16\), and \(D_n\ge1737/200\) for \(n\ge16\).
The supremum envelope's restriction \(m\ge2\) matters:
\(\|H_1\|_\infty=88/63>(8/9)\beta_s\).

The prefactor in \(\mathcal B_m\) is less than one: its square is
\((512/81)/(9+4\sqrt2)<1\). Together with (F.fracgates) and
\(4\beta_f<5\), this yields the useful but weaker comparison bound
\[
 \mathcal B_m^2\le5\beta_f^m.                        \tag{F.fracsimple}
\]
The density formula uses the exact table expression (F.ceilings), not
(F.fracsimple). Jensen and the exact mean also give
\(\mathcal B_m^2\ge\mu^3\); this will check the radial counting domain.

For the sixteen-step fractional bound set
\[
 D_{16,n}^{(3/2)}=b_{16}^{\lfloor n/16\rfloor}b_{n\bmod16},\qquad
 \mathcal B_{16,m}=
 \frac{3(8/9)^{3/2}}{1+2^{3/2}}D_{16,m+1}^{(3/2)},\qquad
 \mathcal B_m^{\rm best}=\min\{\mathcal B_m,\mathcal B_{16,m}\}.
                                                        \tag{F.sixteenceiling}
\]
Inheritance and the same fan identity prove that each is a valid
\(3/2\)-moment ceiling. In particular
\(\mathcal B_m^{\rm best}\ge\mu^{3/2}\). Both fractional ceilings
are retained: their minimum is valid without requiring compatible
extremizers.

### Use of the moment estimates

The finite maximum, second-moment and direct fractional-moment tables
supply the capacity inputs used by the density formulas.
The two transfer implementations use distinct recurrences with the same
reference law and rational table targets. The product inequality extends
these finite bounds to every level. The next section applies them to
actual source weights and logarithmic-time convergence.

## 10. Actual-weight capacity and lower natural density {#chapter10}

The parameterized construction supplies integer trajectories reaching one
at every fixed clock above the reference ratio, with the same root score
(R.score). We now count their distinct starting integers. The aggregate
source-weight bound controls weighted sums in residue classes. An
elementary maximum estimate already gives a common positive density;
the certified moment bounds refine it quantitatively. We count each odd
source together with its even multiples, using the actual source weights
throughout.

### Counting notation {#counting_notation}

The following lookup collects the quantities already defined in the proof.

| Proof stage | Symbols and meanings | Definition |
|---|---|---|
| Integer trajectories | \(w,d,A,C_w,\omega_w\): inverse word, length, total valuation, affine offset and slope weight | (W.inverse), (W.offset), (W.charge) |
| Reference distribution | \(G_q,\mu_q,f_q,\rho_q\): residue group, probability law, density relative to the uniform measure, and its scaled version | (T.law) |
| Approximation | \(\epsilon_m,C_6\): uniform error bound from level \(m\) to finer levels, and its fixed coefficient | (M.constants), (M.envelope) |
| Positive root mass | \(\Pi,V(N),P\): guaranteed reference survival, total future variation bound, and their positive difference | (R.certificate), (R.residual) |
| Root family | \(R_s,W_*\): known convergent roots and a lower bound for their reciprocal-root weighted marked mass | (R.pool), (R.score) |
| Sources and reference factors | \(a_x,H_m\): aggregate weight at integer \(x\), and the weighted reference fan | (N.fan), (N.everyclock) |
| Moment bounds | \(S_m,V_m,\mathcal B_m\): upper bounds for the fan maximum, variance, and average \(3/2\)-power | (F.ceilings) |
| Fractional refinement | \(\mathcal B_{16,m},\mathcal B_m^{\rm best}\): sixteen-step ceiling and the smaller fractional ceiling | (F.sixteenceiling) |
| Density conversion | \(\mathcal D(u)\): lower-density bound from an all-scale harmonic mass \(u\) | (I.conversion), (D.radial) |

The variance bound \(V_m\) is distinct from the seed variation bound
\(V(N)\). In this section \(U\) denotes total source weight, not the
odd accelerated map, and \(T\) denotes a residue-capacity coefficient.

Fix an arbitrary \(c>c_0=3/\log(4/3)\) throughout this section, and write
\[
 \mathcal G_c=\{x\in\mathbb N_{>0}:\tau_1(x)\le c\log x\},
 \qquad \mu=8/9,\quad L=2\log2,\quad\kappa=16\log2/9.
                                                        \tag{D.constants}
\]
The counting density is lower natural density,
\(\underline d(\mathcal G_c)=\liminf_{Y\to\infty}
\#(\mathcal G_c\cap[1,Y])/Y\). The clock is ordinary unaccelerated
Collatz time, and logarithms are natural unless marked \(\log_2\).

### Harmonic sum bound for the source weights

Fix an odd integer modulus \(Q\), a real \(X>0\), a radius \(R>1\),
and a finite set of positive odd integers in \([X,RX)\) carrying weights
\(0\le a_x\le1/x\). Put \(U=\sum_xa_x\) and
\(w_r=\sum_{x\equiv r\ (Q)}a_x\). Odd representatives of one
residue class modulo \(Q\) have spacing \(2Q\). The monotonicity of
\(1/t\) and comparison of all but the first summand with their preceding
intervals give
\[
 \sum_{\substack{X\le x<RX\\x\ {\rm odd},\ x\equiv r\ (Q)}}\frac1x
 \le\frac1X+\frac{\log R}{2Q}.
\]
Equivalently, with
\[
 T_{X,Q,R}=Q/X+\tfrac12\log R,
 \qquad 0\le w_r\le T_{X,Q,R}/Q,                     \tag{D.residuecap}
\]
every nonnegative residue test \(\psi\) satisfies
\[
 \sum_xa_x\psi(x)\le T_{X,Q,R}\langle\psi\rangle_Q.
                                                        \tag{D.harmonic}
\]
Here \(\langle\cdot\rangle_Q\) is the full average modulo \(Q\), namely
\(\langle\psi\rangle_Q=Q^{-1}\sum_{r\bmod Q}\psi(r)\). In this
local notation the subscript is the modulus itself; elsewhere
\(\langle\cdot\rangle_m\) averages modulo \(3^m\).
The proof bounds a weighted subset by an ambient sum; it does not infer
its empirical distribution from a reference law.

Apply this to the source family produced in [the terminal-source section](#chapter05). In addition to
(N.everyclock), its construction gives the actual radius
\(R_X=\mathcal R_{b(X)}=16/(1-8^{-b(X)})\to16\), by
(N.selector) and (N.scales), uniformly in the common cutoff intervals.
The source set is contained in \([X,R_XX)\), before it is enlarged to
any prescribed \([X,\Lambda X)\), \(\Lambda>16\).
For fixed coarse \(m\ge2\), the terminal level \(k=k(X)\)
eventually exceeds \(m\), and \(3^k/X\to0\).

Every \(F_j\) in (F.fan) permutes \(G_k\). The mixing estimate
(T.mix) for \(f\) and the normalization \(\rho=(2/3)f\) yield
\[
 \langle|H_k-H_m\circ\pi_{k,m}|\rangle_k
 \le\frac89\epsilon_m.
                                                        \tag{D.fandiscrepancy}
\]
Indeed, sum the individual discrepancies after the affine permutations;
their factors are \(\sum_{j\ge0}4^{-j}=4/3\). Nonnegativity and
absolute convergence justify exchanging sums and averages. Harmonic
charging at the fine modulus \(3^k\) then proves
\[
 \mathscr A_X\le\sum_xa_xH_m(x)
             +\frac89 T_{X,3^k,R_X}\epsilon_m,
 \qquad T_{X,3^k,R_X}\longrightarrow L.
                                                        \tag{D.coarse}
\]
Thus the limiting error bound is exactly \(\kappa\epsilon_m\). Fixing
\(\Lambda>16\) in the final shell declaration does not replace this
error bound by \((4/9)\log\Lambda\,\epsilon_m\): the physical family
still has its sharper radius tending to sixteen. Conversely, one may not
assume a literal radius sixteen at finite cutoffs.

### Three capacity bounds for the same physical mass

For a fixed level \(m\), let \(Q=3^m\), \(T=T_{X,Q,R_X}\).
The exact mean of \(H_m\) is \(\mu\), and its variance is at most
\(V_m\) from (F.ceilings). Subtract the constant \(U/Q\) from each
residue mass; the centered marker sums to zero. Then
\[
 \sum_r(w_r-U/Q)^2=\sum_rw_r^2-U^2/Q
                  \le(TU-U^2)/Q.
\]
Cauchy--Schwarz, the maximum bound and weighted Hölder give respectively
\[
 \begin{split}
 \sum_xa_xH_m(x)&\le\mu U+\sqrt{V_mU(T-U)},\\
 \sum_xa_xH_m(x)&\le S_m U,\\
 \sum_xa_xH_m(x)&\le U^{1/3}
                   \left(\sum_xa_xH_m(x)^{3/2}\right)^{2/3}
                 \le U^{1/3}(T\mathcal B_m)^{2/3}.
 \end{split}                                        \tag{D.capacity}
\]
The last inequality is (D.harmonic) applied to the nonnegative
\(3/2\)-power. All three bounds use the same actual source weights.
Their validity depends on the source-weight bound (N.charge) established
before the residue masses were formed.

**Proposition (general moment-to-mass conversion).** Let \(s>1\) and
\(B_{s,m}\ge\langle H_m^s\rangle_m\), with \(m\ge2\) fixed.
For a source-family score \(0<W\le27/2^{27}\), set
\(p_m=(W-\kappa\epsilon_m)_+\). Then
\[
 v_{s,m}(W)=
 \frac{p_m^{s/(s-1)}}{(LB_{s,m})^{1/(s-1)}}           \tag{D.generalp}
\]
is a limiting lower bound on the available unmarked source mass:
every \(0\le u<v_{s,m}(W)\) is available at every sufficiently
large scale, for every fixed containing ratio \(\Lambda>16\).

*Proof.* At a finite cutoff, weighted Hölder and (D.harmonic) give
\[
 \sum_rw_rH_m(r)
 \le U^{1-1/s}\bigl(T_{X,3^m,R_X}B_{s,m}\bigr)^{1/s}.
\]
By (D.coarse), the left side is at least
\(W-\eta-\kappa\epsilon_m-o(1)\) for a fixed positive graft
tolerance \(\eta\). Since \(T_{X,3^m,R_X}\to L\), inversion
gives every strict lower bound in (D.generalp) by first choosing a
sufficiently small fixed \(\eta\), then a sufficiently large cutoff.
No positive lower bound is asserted when \(p_m=0\).

Jensen and the mean \(\mu\) give \(B_{s,m}\ge\mu^s>0\). Since
\(p_m\le W<L\mu\),
\[
 v_{s,m}(W)\le
 \frac{p_m}{\mu}
       \left(\frac{p_m}{L\mu}\right)^{1/(s-1)}
 \le\frac W\mu .
\]
This lies in the radial domain (D.domain), by the numerical bounds proved
there. At \(s=3/2\), the formula is exactly
\(p_m^3/(L^2\mathcal B_m^2)\). \(\square\)

The order is denoted by \(s\) here to distinguish it from the residual
marked mass \(p_m\). The quantity \(B_{s,m}\) is a full-group moment,
not an \(s\)-norm. Further certified orders may be used in this
proposition; the optimized formulas here use the direct \(3/2\) tables.

### Using complementary residue capacity

**Proposition (two-sided moment capacity).** Let \(h_r\ge0\) on a
set of \(Q\) residues, with full mean \(\mu\) and
\(\langle h^s\rangle\le B_s\), \(s>1\). Suppose
\(0\le w_r\le T/Q\) and \(\sum_rw_rh_r\ge p\), where
\(0<p<T\mu\). Define \(q_s(p,T)\in(0,p/\mu]\) by
\[
 \frac{p^s}{q_s^{s-1}}+
 \frac{(T\mu-p)^s}{(T-q_s)^{s-1}}=TB_s.             \tag{D.twosidedcapacity}
\]
There is one such solution on that interval, and
\(\sum_rw_r\ge q_s(p,T)\). If \(B_s=\mu^s\), its value is
\(p/\mu\).

*Proof.* Scale the weights down to marked mass exactly \(p\), which
can only decrease their total mass; call the result \(u\).
Complementary weights \(T/Q-w_r\) have total mass \(T-u\) and
marked mass \(T\mu-p\). Hölder on the occupied and complementary
parts, followed by addition, gives
\[
 \frac{p^s}{u^{s-1}}+
 \frac{(T\mu-p)^s}{(T-u)^{s-1}}\le TB_s.            \tag{D.complementholder}
\]
Here \(0<u<T\). On \((0,p/\mu)\) the left side is strictly
decreasing: its derivative has the sign of
\(((T\mu-p)/(T-u))^s-(p/u)^s\). It decreases from infinity to
\(T\mu^s\), which is at most \(TB_s\) by Jensen.
This proves the stated solution and lower bound if \(u<p/\mu\);
if \(u\ge p/\mu\), the lower bound is immediate. \(\square\)

An explicit weaker inverse follows by replacing \((T-u)^{s-1}\)
with its upper bound \(T^{s-1}\):
\[
 \widetilde v_s(p,T)=
 \frac{p^{s/(s-1)}}{
 [T\{B_s-(\mu-p/T)^s\}]^{1/(s-1)}}\le q_s(p,T).
                                                        \tag{D.complementexplicit}
\]
Its denominator is positive. Indeed, putting \(a=p/T\in(0,\mu)\),
\[
 B_s-(\mu-a)^s\ge\mu^s-(\mu-a)^s
                   \ge a\mu^{s-1}>0.
\]
Consequently \(\widetilde v_s(p,T)\le p/\mu\). It strictly
exceeds the occupied-only bound
\(p^{s/(s-1)}/(TB_s)^{1/(s-1)}\), since the subtracted
complementary term is positive.

At a finite cutoff use \(T=T_{X,3^m,R_X}\), the actual capacity
coefficient, and a guaranteed positive marked mass below
\(W-\eta-\kappa\epsilon_m-o(1)\). First fix a sufficiently small
graft tolerance \(\eta\), then take the cutoff large. Continuity
as \(T\to L\) gives every strict lower bound below the displayed
inverse with \(p=p_m=(W-\kappa\epsilon_m)_+\), \(T=L\).
Set the inverse to zero when \(p_m=0\). The bound by \(p_m/\mu\)
also gives continuity there and keeps it in (D.domain). Thus the
same radial counting applies; no limiting capacity is imposed at a
finite cutoff.

Fix a score \(0<W\le W_{\max}:=27/2^{27}\) for which the local
source-family theorem holds. Set
\[
 p_m=(W-\kappa\epsilon_m)_+,
 \quad B_m(p)=2\mu p+V_mL,
\]
\[
 \Psi_m(p)=\frac{2p^2}{B_m(p)+
        \sqrt{B_m(p)^2-4(\mu^2+V_m)p^2}},\qquad
 \Psi_m(0)=0,                                       \tag{D.inverse}
\]
\[
 u_m^{\rm MV}(W)=\max\{\Psi_m(p_m),p_m/S_m\},\qquad
 v_m(W)=\frac{p_m^3}{L^2\mathcal B_m^2},\qquad
 u_m(W)=\max\{u_m^{\rm MV}(W),v_m(W)\}.              \tag{D.massrecipe}
\]
The stronger branches and their common maximum are
\[
 \begin{aligned}
 v_{16,m}(W)&=\frac{p_m^3}{L^2\mathcal B_{16,m}^2},\\
 \widetilde v_m(W)&=
 \frac{p_m^3}{L^2[\mathcal B_m^{\rm best}-(\mu-p_m/L)^{3/2}]^2}
             \quad(p_m>0),\qquad \widetilde v_m(W)=0\quad(p_m=0),\\
 u_{16,m}(W)&=\max\{u_m(W),v_{16,m}(W)\},\\
 u_m^{\rm comp}(W)&=\max\{u_{16,m}(W),\widetilde v_m(W)\}.
 \end{aligned}                                        \tag{D.refinedmass}
\]
The complementary branch uses the better of the two moment ceilings.
All branches concern the same actual source family and fixed score.
Their limiting mass bounds are at most \(W/\mu\), as are the
original branches by (D.domain).

The label \({\rm MV}\) denotes the combination of the centered
second-moment and maximum bounds; it does not change the root score or
mixing estimate. The added term \(v_m(W)\) is the direct fractional-moment
bound. Each expression estimates the same unmarked source mass.
The square root and its choice of branch have the following justification.
On \([0,L/2]\), the function
\(g_m(u)=\mu u+\sqrt{V_mu(L-u)}\) is strictly increasing, with
\(g_m(0)=0\) and \(g_m(L/2)\ge\mu L/2>W_{\max}\).
Consequently there is a unique inverse for \(0\le p\le W_{\max}\).
Squaring on the branch \(p-\mu u\ge0\) gives
\[
 (\mu^2+V_m)u^2-(2\mu p+V_mL)u+p^2=0.
\]
The required solution is the smaller root, whose rationalized expression
is (D.inverse). It obeys \(\Psi_m(p)\le p/\mu<L/2\).
Choosing the other quadratic root would assert a false capacity bound.

The radial domain will also be respected. Since \(S_m\ge\mu\), both
benchmark branches are at most \(W/\mu\). Jensen in (F.fanmoments) gives
\(\mathcal B_m^2\ge\mu^3\). Since \(\log2>2/3\),
\(L^2\mu^3>(16/9)(512/729)>1\). Therefore \(v_m\le W^3\le W\).
In particular
\[
 0\le u_m(W)\le W/\mu
 <\tfrac12\log(3/2)<L/2.                            \tag{D.domain}
\]
The strict numerical inequality follows already from
\(W_{\max}/\mu<1/100\) and
\(\tfrac12\log(3/2)>1/6\), the latter by integrating \(1/t>2/3\)
on \([1,3/2)\).

**Lemma (all-scale unmarked mass).** For each fixed \(m\ge2\), each
\(u<u_m(W)\) with \(u\ge0\), and each fixed \(\Lambda>16\),
every sufficiently large real \(X\) has a finite family of odd sources
in \(\mathcal G_c\cap[X,\Lambda X)\), with
\[
 a_x\le1/x,\qquad\sum_xa_x\ge u.                    \tag{D.mass}
\]

*Proof.* Fix \(m,\Lambda\) and a positive graft tolerance \(\eta\).
(N.everyclock) and (D.coarse) give coarse marked mass at least
\(W-\eta-\kappa\epsilon_m-o(1)\); both fine and coarse capacity
coefficients tend to \(L\), uniformly at large cutoffs. Apply
(D.capacity). To justify the limit without postulating one zero-error
graft, first allow \(\eta\downarrow0\) in these scalar inequalities.
If an asserted branch lower bound failed by a fixed positive amount for
every sufficiently small tolerance, one could choose \(\eta_i\to0\)
and corresponding sufficiently large bad cutoffs. Their masses have a
convergent subsequence, since \(U\le T\to L\). The limit \(U_*\)
would satisfy all three inequalities with left side \(p_m\) and
capacity \(L\). If \(U_*\ge L/2\), (D.domain) already contradicts
the failure; otherwise monotonicity of \(g_m\) and the other two
inversions give \(U_*\ge u_m(W)\), again a contradiction. Hence a
single sufficiently small fixed tolerance and a single associated finite
graft work for the chosen strict \(u\) and all large \(X\).
At \(p_m=0\), all the asserted branch bounds are zero and there is
nothing positive to prove. \(\square\)

The same conclusion (D.mass) holds for every \(0\le u<u_m^{\rm comp}(W)\).
For the sixteen-step branch use (D.generalp) with (F.sixteenceiling);
for the complementary branch use the finite-cutoff argument after
(D.complementexplicit). A finite maximum of valid limiting mass bounds
remains valid by choosing an attaining branch and its fixed tolerance.
All lie in (D.domain).

These bounds give the explicit density recipes below.
[Appendix D.2](#appendix_profiles) gives the stronger finite allocation
problem using the whole concentration profile, without asserting a new
numerical value for the optimized constant.

### Joint harmonic allocation and dyadic counting

The *dyadic tower* of an odd integer is the set of its multiples by
nonnegative powers of two. We keep these multiples and their source weights
together when converting harmonic mass into an integer count.

For positive \(x\le Y\), let
\[
 D_Y(x)=1+\lfloor\log_2(Y/x)\rfloor.
                                                        \tag{D.dyadic}
\]
This is the number of members of that tower at most \(Y\).
Distinct odd integers have disjoint dyadic towers. Also \(\mathcal G_c\)
is closed under multiplication by powers of two: for \(r\ge0\),
\(\tau_1(2^rx)\le r+\tau_1(x)\), and
\(c\log2>c_0\log2>1\). Thus all the counted towers remain inside the
same literal logarithmic-time set.

**Theorem (conversion from small harmonic mass to lower density).** Suppose, for every fixed
\(R>16\) and every sufficiently large real \(X\), the odd members
of a dyadically closed set \(G\) in \([X,RX)\) admit weights
\(0\le a_x\le1/x\) totaling at least \(u\). If
\(0\le u\le\tfrac12\log(3/2)\), then
\[
 \underline d(G)\ge \mathcal D(u):=\frac{32}{225}(e^{2u}-1).
                                                        \tag{D.radial}
\]

The function \(\mathcal D\), introduced in (I.conversion), converts
weighted counts over intervals of sizes comparable to \(X\) into density
below a final cutoff. We call it the radial conversion.

*Proof.* The zero case is immediate. First consider one exact band
\((X_j,16X_j)\), where \(X_j=Y/16^j\), \(j\ge1\) is fixed.
Away from its four dyadic boundaries, the tower count on
\((2^hX_j,2^{h+1}X_j)\) is \(4j-h\), for \(h=0,1,2,3\).
Relax integer selection to occupations \(0\le t_x\le1\) at all
ambient odd points, taking \(t_x=xa_x\) on the actual family and
zero elsewhere. Their harmonic mass is \(\sum t_x/x\), and their
fractional counting cost is \(\sum t_xD_Y(x)\). The actual integer
count is at least that cost.

The cost per unit harmonic mass is \(xD_Y(x)\). In the first subband
it increases as \(4jx\). The minimum in any later subband is at least
\(2^h(4j-h)X_j\ge(8j-2)X_j\ge6jX_j\).
For fixed \(1<s<3/2\), all odd points in \((X_j,sX_j)\) therefore
cost no more per unit mass than any remaining point. An exchange of
harmonic mass from a dearer occupied point to a cheaper unfilled one
cannot increase cost. At a prescribed small mass the relaxed minimum is
thus obtained by filling the odd points nearest the bottom, with at most
one partial occupation, up to the required level.

Uniform integral comparisons and odd spacing give
\[
 \sum_{\substack{X_j<x<sX_j\\x\ {\rm odd}}}\frac1x
       =\tfrac12\log s+O(X_j^{-1}),\qquad
 \#\{x\text{ odd}:X_j<x<sX_j\}
       =\tfrac12(s-1)X_j+O(1).                      \tag{D.bandcensus}
\]
If the prescribed mass tends to \(a\) with
\(0<a<\tfrac12\log(3/2)\), take \(s=e^{2a}\).
The \(O(X_j^{-1})\) discrepancy in mass changes the minimum cost by
only \(O(j)\): each available point near this fixed level has mass
of order \(X_j^{-1}\) and cost of order \(j\). It follows that
every occupation of mass at least \(a-o(1)\) costs at least
\[
 2j(e^{2a}-1)\frac{Y}{16^j}-o(Y).                   \tag{D.bandcost}
\]
At the upper endpoint use every smaller \(a\) and let it increase
to the endpoint. Removing the finitely many dyadic boundary points costs
only \(O(X_j^{-1})\) harmonic mass; their extra tower copies cannot
weaken a lower count. Thus (D.bandcost) covers all boundary conventions.

The available shells do not have exact radius sixteen. Fix a packing
depth \(J_0\ge1\) and a fixed \(R>16\), then choose the hypothesized
families in the pairwise disjoint shells
\([Y/R^j,Y/R^{j-1})\), \(1\le j\le J_0\). Remove sources below
\(Y/16^j\). At most
\[
 \frac j2\log(R/16)+O(Y^{-1})                       \tag{D.stripdebit}
\]
of harmonic mass is lost, by the same odd census, with constants allowed
to depend on the fixed \(j,R\). The remainder lies in the exact band
\([Y/16^j,Y/16^{j-1})\). Its mass is at least
\(a_j-o(1)\), where \(a_j=(u-\tfrac j2\log(R/16))_+\).
For each positive \(a_j\), apply (D.bandcost) with an arbitrarily small
fixed downward tolerance; the zero cases contribute zero. The selected
odd sources in different shells are distinct and their towers are disjoint.
After dividing their total count by \(Y\), first let \(Y\to\infty\),
then \(R\downarrow16\) with \(J_0\) fixed, and finally
\(J_0\to\infty\). All inequalities concern the same set \(G\),
so source families and startup cutoffs may depend on these fixed choices.
Since \(\sum_{j\ge1}4j/16^j=64/225\), the result is
\[
 \underline d(G)\ge\frac{e^{2u}-1}{2}
       \sum_{j\ge1}\frac{4j}{16^j}
       =\frac{32}{225}(e^{2u}-1).
\]
This proves (D.radial). \(\square\)

The linear consequence is \(\mathcal D(u)\ge64u/225\), which retains the
factor \(32/15\) over the older separate packing-and-doubling
coefficient \(2u/15\). The nonlinear expression is stronger still,
but its ratio to the linear one tends to one as \(u\downarrow0\).
No extra fixed multiplicative improvement is claimed from that small
second-order correction.

### A common positive density without finite moment certificates

**Proposition (elementary common-density bound).** Suppose (T.mix) has
\(\epsilon_m\to0\), and a fixed persistent pool supplies a score
\(0<W\le W_{\max}=27/2^{27}\) for (N.everyclock).
Choose one fixed \(m\ge2\) such that \(\kappa\epsilon_m<W/2\).
Then
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c)\ge\frac{4W}{25\,2^m}>0.
                                                        \tag{D.elementarydensity}
\]
Both \(W\) and \(m\) are fixed before \(c\). This deduction uses
no moment certificates at level twelve or sixteen.

*Proof.* Such an \(m\) exists because \(\epsilon_m\to0\).
The elementary recursion (B.markercap) and the fan definition (F.fan)
give
\[
 \|H_m\|_\infty
 \le\sum_{j\ge0}4^{-j}\|\rho_m\|_\infty
 \le\frac89\,2^m.                                    \tag{D.elementarycap}
\]
For a fixed \(c>c_0\), the source theorem (N.everyclock) and
(D.coarse) therefore supply every mass strictly smaller than
\[
 \frac{W-\kappa\epsilon_m}{(8/9)2^m}
 >a_m:=\frac{9W}{16\,2^m}.
\]
Indeed, for a fixed positive graft tolerance \(\eta\), the finite
coarse marked mass is at least \(W-\eta-\kappa\epsilon_m-o(1)\).
First make \(\eta\) small enough for the desired strict mass, then take
all cutoffs sufficiently large. This works for every fixed containing
ratio \(\Lambda>16\), using the actual radius tending to sixteen.

Since \(m\ge2\), \(a_m<W\le W_{\max}<1/100\); also
\(\tfrac12\log(3/2)\ge1/6\), by integrating \(1/t\ge2/3\)
on \([1,3/2]\). Thus every \(0<u<a_m\) is in the radial domain.
The set \(\mathcal G_c\) is dyadically closed as proved above.
Apply (D.radial), let \(u\uparrow a_m\), and use continuity and
\(\mathcal D(u)\ge64u/225\):
\[
 \underline d(\mathcal G_c)\ge\mathcal D(a_m)
 \ge\frac{64}{225}\frac{9W}{16\,2^m}
 =\frac{4W}{25\,2^m}.
\]
The fixed score and coarse level have no dependence on \(c\); the
graft and eventual cutoff may have such a dependence. \(\square\)

### Explicit density bounds

Define
\[
 c_{\rm MV}(W)=\max_{m\ge2}\mathcal D(u_m^{\rm MV}(W)),\qquad
 c_{\rm FM}(W)=\max_{m\ge2}\mathcal D(u_m(W)).                 \tag{D.densityrecipe}
\]
The two refinements are
\[
 \begin{aligned}
 c_{{\rm FM},16}(W)&=\max_{m\ge2}\mathcal D(u_{16,m}(W)),\\
 c_{\rm comp}(W)&=\max_{m\ge2}\mathcal D(u_m^{\rm comp}(W)).
 \end{aligned}                                        \tag{D.refinedrecipe}
\]
Here \({\rm comp}\) denotes complementary residue capacity.

Here \({\rm FM}\) stands for fractional moment. The two formulas
\(c_{\rm MV}\) and \(c_{\rm FM}\) optimize
the same score, finite tables, mixing error bound and counting function;
only the fractional-moment branch is omitted from \(c_{\rm MV}\).
These are the complete optimized formulas, rather than the simpler
exponential upper bounds used to compare them.

**Theorem (quantitative density at every larger clock).** With the
canonical primitive input (M.primitive), survival theorem (R.certificate)
and finite certificates (F.finitetarget), every source-family score
\(0<W\le W_{\max}\) from a fixed convergent antichain satisfies
\[
 \begin{aligned}
 \underline d(\mathcal G_c)&\ge c_{\rm comp}(W)
      \ge c_{{\rm FM},16}(W)\\
      &\ge c_{\rm FM}(W)\ge c_{\rm MV}(W)>0
             \qquad(c>c_0).
 \end{aligned}                                        \tag{D.headline}
\]
In particular the baseline score \(W_*\) gives
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c)\ge c_{\rm FM}(W_*)>0.     \tag{D.everyclock}
\]
All scores and density functions are independent of \(c\).
The same implications hold for any fixed integer \(C\ge1\) satisfying
(M.primitive), with its corresponding mixing, startup and score recipes.
For fixed \(c>c_0\) and any strict lower bound \(d<c_{\rm comp}(W)\),
all sufficiently large \(X\) have
\(\#(\mathcal G_c\cap[1,X])\ge dX\).

*Proof.* The reference-mixing, seed-mark and persistent-root sections
provide the graft premises: (R.graftinput) discharges (G.marks), and
(N.everyclock) supplies all-scale source families in the fixed set
\(\mathcal G_c\). For each \(m\), use (D.mass) and its extension
to (D.refinedmass), followed by (D.radial). Let the strict mass bound
increase to the corresponding limiting value and use continuity of
\(\mathcal D\). Taking the supremum gives each density formula.

Each supremum is a positive attained maximum. The error envelope tends
to zero, so \(p_m>0\) eventually. The maximum branch tends to zero by
(F.spike), and the centered inverse tends to zero since \(V_m\to\infty\)
and \(\Psi_m\le2W^2/(V_mL)\). Both fractional branches tend to zero
because \(b_{12},b_{16}>1\). Finally
\(\mathcal B_m^{\rm best}\to\infty\); once it exceeds
\(2\mu^{3/2}\),
\[
 \widetilde v_m(W)\le4\max\{v_m(W),v_{16,m}(W)\}\longrightarrow0.
\]
This follows by bounding the subtracted complementary term by
\(\mu^{3/2}\). Thus each positive mass sequence tends to zero and
attains its supremum at a finite level. Inclusion of branches proves
the non-strict comparisons. Section 11 proves the strict improvements.

The pool and score precede \(c\) by (N.everyclock); none of
\(L,\kappa,\epsilon_m\), the moment ceilings or the optimizations
depends on \(c\). Only the graft and eventual cutoffs do. The final
counting assertion is the definition of lower density. In particular,
\(c=10431/1000\) gives the certified numerical specialization. \(\square\)

**Corollary (an unspecified vanishing clock loss).** If a constant
\(d_0>0\) satisfies the common-clock conclusion above, there exists
a nonincreasing \(\eta:[1,\infty)\to(0,\infty)\), with
\(\eta(x)\to0\), such that
\[
 \underline d\{x\ge1:\tau_1(x)\le(c_0+\eta(x))\log x\}
          \ge d_0.                                  \tag{D.vanishingclock}
\]
In particular one set of lower density at least \(d_0\) has
\(\limsup_{x\to\infty}\tau_1(x)/\log x\le c_0\), with the limit
restricted to that set. No decay rate for \(\eta\) is specified.

*Proof.* Put \(A_j=\mathcal G_{c_0+1/j}\); these sets decrease with
\(j\). Choose strictly increasing integer cutoffs \(X_j\ge j\)
such that \(\#(A_j\cap[1,X])\ge(d_0-1/j)X\) for every
\(X\ge X_j\). Set \(\eta=1/j\) on \([X_j,X_{j+1})\) and
\(\eta=1\) below \(X_1\). If \(X\) is in the \(j\)-th band,
every point of \(A_j\) below \(X\) satisfies the new clock bound:
its earlier band has allowance at least \(1/j\). The resulting set
therefore has at least \((d_0-1/j)X\) points below \(X\).
Let \(X\to\infty\). This diagonalization uses the nested fixed-clock sets; the endpoint
\(c=c_0\) is discussed in Section 5.
The same proof applies to any fixed target with a common density
constant throughout \(c>c_0\). \(\square\)

**Theorem (finite-pool transfer to a fixed target).** Under the same
analytic and moment inputs as (D.everyclock), fix a positive
target \(y_\star\) and a nonempty finite pool satisfying (G.marks),
(W.antichain), and the finite root-to-target path hypothesis of
(N.targetfamily). If \(0<W\le W_{\max}\), then
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c(y_\star))\ge c_{\rm comp}(W)
                              \ge c_{\rm FM}(W)>0.
                                                        \tag{D.finitepool}
\]
Without the moment-table premise, the same pool gives the elementary
bound (D.elementarydensity),
with \(\mathcal G_c(y_\star)\) replacing \(\mathcal G_c\).

*Proof.* Apply (N.targetfamily). Every step of the harmonic-capacity and
coarse-transfer argument uses its source weights, radius and precision;
none depends on which fixed target is eventually visited.
The target-clock set is dyadically closed because
\(\tau_{y_\star}(2^rx)\le r+\tau_{y_\star}(x)\) and \(c\log2>1\).
Thus (D.mass), including its refined branches, the general set formulation
of (D.radial), and the attainment argument in (D.headline) give the bound.
The elementary maximum argument proves the table-free variant. The
pool, score and coarse estimates precede \(c\), so one constant works
throughout its stated range. \(\square\)

**Corollary (odd sources in every large shell).** Fix \(c>c_0\),
\(\Lambda>16\), \(m\ge2\), and \(0<u<u_m(W)\) for a
score in (D.everyclock). Then for all sufficiently large real \(X\),
\[
 \#\{x\in\mathcal G_c\cap[X,\Lambda X):x\text{ odd}\}
       \ge uX.                                      \tag{D.shellcount}
\]
Indeed, (D.mass) as used above supplies unmarked mass at least \(u\),
and each source has weight at most \(1/X\). Marked mass alone would
not give this count. The assertion uses \(\Lambda>16\) and a strict
mass below the limiting bound.

### Every prescribed target not divisible by three {#fixed_targets}

Two complete incoming periods suffice for the general target theorem.

**Theorem (every fixed positive unit target).** For every positive
integer \(y_\star\), \(3\nmid y_\star\), an effectively defined \(d_{y_\star}>0\)
satisfies
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c(y_\star))\ge d_{y_\star}.
                                                        \tag{D.everytarget}
\]

*Proof.* Use the selected startup \(N\) and \(q=q_N\), as in
(R.markapplication). Write \(y_\star=2^v y\), with \(y\) odd. In
(W.constructor), choose \(t_0\ge0\) so that \(X_{t_0}(y)\ge16^b\) and
\(2t_0+e(y)\ge v+1\). Take the unit roots in each of the disjoint
index intervals
\([t_0,t_0+3^q)\) and \([t_0+3^q,t_0+2\cdot3^q)\).
Each contains one root in every unit residue. All roots have next odd
value \(y\). By the cycle-predecessor lemma of Section 1, at most one
root in their union is periodic. At least one whole block therefore
satisfies (W.antichain).

Let
\[
 M_{\max}=X_{t_0+2\cdot3^q-1}(y),\qquad
 W_{y_\star}=\min\{W_{\max},K_qP/M_{\max}\}>0,\qquad
 d_{y_\star}=c_{\rm FM}(W_{y_\star}).                  \tag{D.targetscore}
\]
The identity (B.physical), uniform over roots, and full future variation bound
(R.latermarks) give \(z_r=(g_N(r)-V(N))_+\) on either block, with
\(\sum_rz_r\ge K_qP\). Hence the suitable block has
\(\sum_Mz_M/M\ge K_qP/M_{\max}\). Its root indexed by \(t\) reaches
\(y_\star\) along the ordinary odd-and-halving segment in
\(1+2t+e(y)-v\) steps. These specified finite paths need no information
about the orbit after \(y_\star\). Apply (D.finitepool).

The score recipe is effective and the same for either candidate block;
no cycle-detection procedure is needed to define it or to prove that
one block is suitable. All choices are finite and precede \(c\).
With the qualitative analytic input, (D.elementarydensity) instead gives
\(4W_{y_\star}/(25\,2^m)>0\) at one fixed \(m\) making the mixing error smaller than half the score,
without the large moment tables. \(\square\)

This proves (I.targets). It does not assert convergence of the target.

**Corollary (one-period quantitative target score).** Retain the selected
startup \(q=q_N\), \(K=K_q\), \(B=B_q\), \(P=\Pi-V(N)\) and
the index \(t_0\) of the preceding proof. Set
\[
 M_1=X_{t_0+3^q-1}(y),\qquad
 W_{y_\star}^{\rm one}=\frac{KP-B}{M_1}.
                                                        \tag{D.oneperiodscore}
\]
Then \(0<W_{y_\star}^{\rm one}<2^{-4096}\), and
\[
 \forall c>c_0:\qquad
 \underline d(\mathcal G_c(y_\star))
       \ge c_{\rm comp}(W_{y_\star}^{\rm one})>0.      \tag{D.oneperioddensity}
\]
Its score strictly improves the two-period value in (D.targetscore):
\[
 \frac{W_{y_\star}^{\rm one}}{W_{y_\star}}
                         >\tfrac12\,4^{3^q}.        \tag{D.oneperiodgain}
\]

*Proof.* Equations (R.denominator) and (R.conductorguards), with
\(b=2^{25}\), \(N\ge16\), and \(3/2>\sqrt2\), give
\[
 \frac{KP}{B}=P(3/2)^q
 >2^{q/2-1575N-6305}
 \ge2^{(b/2-1575)N-6305}>2.                          \tag{D.singlecap}
\]
The last exponent is at least \(268403951\). One full unit period
has persistent marks totalling at least \(KP\). Remove its periodic
root if present. There is at most one, so its removal costs at most
\(B\); the remaining pool is nonempty and satisfies (W.antichain).
It retains the specified finite paths to the actual target, including
its even factor. Root-uniform persistence gives score at least
\((KP-B)/M_1\). Apply (D.finitepool).

For the domain, put \(T=3^q\). The recurrence
\(X_{t+1}(y)=4X_t(y)+1\) gives \(M_1\ge16^b4^{T-1}\), while
\(KP<K<T\) and \(T/4^{T-1}<1\). Hence
\(W_{y_\star}^{\rm one}<16^{-b}<2^{-4096}\).
If \(M_2=X_{t_0+2T-1}(y)\), the same recurrence gives
\[
 M_2=4^TM_1+(4^T-1)/3>4^TM_1.
\]
The clipping in (D.targetscore) is inactive by the same domain bound.
Since \(KP-B>KP/2\), division proves (D.oneperiodgain).
The score is a finite rational recipe; no cycle-decision procedure is
needed to define it. The two-period construction remains available for
the qualitative theorem without the scalar cap comparison. \(\square\)

**Corollary (exact obstruction to positive-density hitting).** For every
positive integer \(y\) and every fixed \(c>c_0\),
\[
 \boxed{\underline d(\mathcal G_c(y))>0
        \quad\Longleftrightarrow\quad 3\nmid y.}       \tag{D.targetcriterion}
\]

*Proof.* If \(3\nmid y\), apply (D.everytarget). Suppose \(3\mid y\).
An odd predecessor of a number divisible by three is impossible, since
\(3x+1\equiv1\pmod3\). Its only predecessor is therefore its double,
which is again divisible by three. Iterating this observation backwards
along any finite path, and conversely taking repeated halvings, gives
\[
 \begin{aligned}
 \{x\ge1:\tau_y(x)<\infty\}&=\{2^j y:j\in\mathbb Z_{\ge0}\},\\
 \#\{x\le X:\tau_y(x)<\infty\}
   &=1+\left\lfloor\log_2(X/y)\right\rfloor
     =O_y(\log X)\qquad(X\ge y).
 \end{aligned}                                       \tag{D.divisiblepredecessors}
\]
The full predecessor basin has natural density zero, and so does its
subset \(\mathcal G_c(y)\). \(\square\)

There can be no positive density constant uniform over all admissible targets:
the predecessor basins of the infinitely many distinct \(R_s>1\)
with \(3\nmid s\) are pairwise disjoint, and these targets are units
modulo three. If any \(J\) such basins each had lower density
at least \(d>0\), their union would have lower density at least \(Jd\le1\).
Letting the finite number \(J\) increase rules out a common positive \(d\).

**Remark (a score from one persistent root).**
At least one root \(M\) from (R.pool) has a fixed score \(W_M>0\)
such that, for every \(c>c_0\),
\[
 \underline d\{x:\tau_M(x)\le c\log x\}
       \ge c_{\rm FM}(W_M)>0,                        \tag{D.roottarget}
\]
where \(\tau_M\) is the least ordinary hitting time of \(M\).

*Proof.* By (R.persistence), \(\sum_s z_s\ge K_qP>0\).
Choose the first \(s\), in increasing order in the finite set
\(\mathcal S_q\), with \(z_s>0\), put \(M=R_s\), and take
\(W_M=\min\{z_s/M,W_{\max}\}>0\). These are finite rational
operations, although no numerical target is evaluated here. The singleton
pool obeys (G.marks) with that score. Every constructed inverse history
passes through \(M\), so its bound on time to one also bounds its
time to \(M\). The latter logarithmic-time set is dyadically closed.
Repeat the proof of (D.everyclock) for this set. This singleton argument
selects a positive entry of the persistent vector; it does not assert
that every entry is positive. \(\square\)

**Remark (one-block construction for a convergent target).** For every
fixed convergent odd unit \(y\), the set \(\mathcal G_c(y)\) has positive lower natural density,
with one target-dependent constant for all \(c>c_0\).
Indeed choose a barrier exceeding \(16^b\) and every odd state on the
finite trajectory of \(y\). A complete period of the roots \(X_t(y)\)
above that barrier is residue-complete and a convergent antichain:
after its first odd step every later odd state is below the barrier.
The persistent vector has positive total mass on this block.
Apply (D.finitepool) with target \(y\).

**Corollary (qualitative analytic input).** A single positive lower
density bound for all \(c>c_0\) follows from the local primitive theorem
and the seed, persistent-root, graft and terminal constructions, without
the large finite moment certificates. Alternatively, Tao's published
reference-law estimates [1] suffice without specifying a numerical
analytic coefficient.

*Proof.* For the local route, (E.primitive) supplies (M.primitive), Section 6
gives its mixing envelope, and Sections 7–8 give a fixed positive score.
Choose one coarse level at which the error is less than half the score,
and apply (D.elementarydensity). This needs no large moment certificate.

For the alternative route, [1, Proposition 1.17] applied at order \(6409\)
gives (M.primitive) for an integer coefficient \(C\ge1\), with the Fourier
sign changed by conjugation when necessary. Section 6 and the finite startup
argument then give a positive score \(W(C)\).

Alternatively, [1, Proposition 1.14] supplies (T.mix) with unhalved error
\(K_A m^{-A}\). Take \(A=2314/25\) and an integer
\(\widehat C>\max\{K_A,2^{8838}\}\). The envelope in
(B.coefficientscope), the survival bound \(\Pi=24/25\), and the root
allocation give a positive score. In either case decrease the score into
\((0,W_{\max}]\), choose a coarse level with error less than half that score,
and apply (D.elementarydensity).

In every route the coefficient, pool, score and coarse level are fixed
before \(c\). The law and norm are those of (T.law) and (T.mix). \(\square\)

The alternative scores depend on their chosen analytic coefficients.
The explicit density formulas use \(C_{\rm primitive}\) and the finite
tables of Section 9.

**Corollary (explicit rational specialization).** For rational
\(0<W\le W_{\max}\) satisfying the source-family theorem, let
\[
 m_\circ=\max\left\{2,\left\lceil
       \left(\frac{5C_6}{2W}\right)^{25/2314}\right\rceil\right\}.
\]
Then the bound announced in (I.rational) holds:
\[
 c_{\rm FM}(W)>
       \frac4{1125}W^3(57/50)^{-m_\circ}.             \tag{D.explicit}
\]

*Proof.* The chosen envelope obeys
\(\epsilon_{m_\circ}\le C_6m_\circ^{-2314/25}\le2W/5\).
Since \(\kappa=16\log2/9<100/81<5/4\), its residual
\(p_{m_\circ}\) is strictly greater than \(W/2\).
Using \(L^2<2\), (F.fracsimple), and the fractional branch in
(D.massrecipe), gives
\[
 u_{m_\circ}(W)>
       \frac{W^3}{80(57/50)^{m_\circ}}.
\]
The inequality \(\mathcal D(u)\ge64u/225\) proves (D.explicit).
The logarithmic bounds used here follow from \(\log2<25/36\);
then \(L^2<(25/18)^2<2\).
For the canonical integer \(C_6\) and rational \(W\), the least
integer in the ceiling is determined by
\[
 m^{2314}(2W)^{25}\ge(5C_6)^{25}.
\]
Clearing denominators makes this an integer comparison. The recipe
terminates, although its integers are not of practical size. \(\square\)

For any constant strictly below the displayed density bound, the proof
supplies an eventual all-cutoff lower bound with that constant. A lower
density liminf alone does not assert exact attainment of the displayed
constant at every sufficiently large finite cutoff. Neither the fixed
root pool nor the finite coarse precision is chosen anew at each cutoff.

The estimate combines the source-family theorem, the reference-moment
bounds and the counting argument above. Its analytic input is the
primitive Fourier theorem (M.primitive); the survival and moment
certificates supply the stated finite inequalities. It remains to quantify
the improvement over the formula without fractional moments.

## 11. Quantifying the fractional-moment improvement {#chapter11}

We first compare the twelve-step fractional-moment formula with the
optimized maximum and second-moment bounds. Its fractional branch has
slower growth in the ternary level, but contains an extra power of the
small marked mass; the comparison must account for both effects. We then
prove the strict improvements from sixteen-step propagation and
complementary capacity, retaining the same mixing envelope (M.envelope).

### Two properties of the certified error envelope

For every integer \(n\ge2\), the explicit formula (M.envelope) satisfies
\[
 \epsilon_n\ge\frac1{300}n^{-95},\qquad
 \epsilon_m\le\frac nm\epsilon_n
       \quad(m\ge n\ge2,\ \epsilon_n<2).            \tag{Q.error}
\]
These inequalities describe the envelope (M.envelope).

To prove them, use \(\log2<25/36\). Throughout the compact range
\(80\le v\le679/5\), one has \(q_v<95\) and \(a(v)>1\),
while \(A=2314/25<95\). The latter exponent bound follows already
from \(6407-(25/72)(679/5)^2>1\). Every nonconstant candidate in
(M.envelope) therefore decreases at least as \(x^{-1}\); in the
second term of (M.widthbound), \(q_v>2\) and \(1/\log x\) is
also decreasing. If \(\epsilon_n<2\), a nonconstant candidate attains
that minimum. It remains available at every larger level, including
when crossing \(m_0\), where more choices are added. This proves the
second assertion. Compactness and continuity ensure attainment of the
width minimum.

For the first assertion, the second positive term of each compact-width
candidate is at least
\[
 \frac{32}{95^2}n^{-95}>\frac1{300}n^{-95},
\]
using \(\log n\le n\) and \(q_v<95\). The constant two and
\(C_6n^{-A}\), with \(C_6\ge1\), also exceed this floor. Taking
the minimum proves (Q.error) without estimating the actual reference
discrepancy from below.

### A bound for the maximum and second-moment formula

Fix \(0<W\le2^{-4096}\), put \(a=\log_2(1/W)\), and let
\[
 n=\min\{m\ge2:W>\kappa\epsilon_m\}.
                                                        \tag{Q.firstpositive}
\]
This minimum exists because \(\epsilon_m\to0\). Since \(\kappa>1\),
(Q.error) implies \(W>n^{-95}/300\), and hence
\[
 n>2^{(a-9)/95}>1000(2a+32),\qquad n>32.
                                                        \tag{Q.largeconductor}
\]
For the second inequality, at \(a=4096\) the middle expression exceeds
\(2^{43}>1000(2\cdot4096+32)\). The logarithmic derivative of its
ratio to \(2a+32\) is
\((\log2)/95-1/(a+16)>1/190-1/4112>0\) thereafter.
The constant \(\kappa>1\) follows from \(\log2>2/3\).

For the collision table, exact rational comparisons give
\[
 e_{16}>(8/7)^{16},\qquad
 \frac{64}{135}(7/8)^{14}>\frac1{16}.
\]
Because every remainder \(e_r\ge1\), writing
\(m+1=16s+r\), \(0\le r<16\), yields
\[
 (64/135)D_{m+1}\ge\frac1{16}(8/7)^m.
\]
At \(m\ge32\) this exceeds \(2\mu^2\), so
\[
 V_m\ge\frac1{32}(8/7)^m.                            \tag{Q.variancefloor}
\]
This is a lower bound for the ceiling \(V_m\).

If \(U=\Psi_m(p_m)\), the correct inverse relation in (D.inverse)
gives \(p_m=\mu U+\sqrt{V_mU(L-U)}\), with \(U<L/2\).
Thus \(U\le2p_m^2/(V_mL)\le64W^2(7/8)^m\), since \(L>1\).
The other benchmark branch obeys
\(p_m/S_m\le(3/2)W(2/3)^m\), by (F.spike), since \(S_m\)
is a valid upper bound for that maximum. All branches vanish at \(m<n\).
For every \(m\ge n\), both benchmark branches are at most
\(64W(7/8)^n\). Their actual masses are also less than \(1/2\),
by (D.domain). On \(0\le u\le1/2\), convexity of the exponential
and \(e<3\) give \(e^{2u}-1\le2(e-1)u<4u\).
Here \(e<3\) follows by summing \(1/k!\le2^{-(k-1)}\) for
\(k\ge2\), with strict inequality at \(k=3\). Therefore
\[
 c_{\rm MV}(W)\le\frac{8192}{225}W(7/8)^n.
                                                        \tag{Q.oldbound}
\]
The comparison bounds the formula \(c_{\rm MV}\).

### Strict improvement over the optimized benchmark

Choose \(m=\lceil101n/100\rceil\), solely for this comparison; the
headline still optimizes all levels. The definition of \(n\) implies
\(\epsilon_n<W/\kappa<2\), so (Q.error) proves
\[
 p_m=W-\kappa\epsilon_m>W(1-n/m)\ge W/101.
                                                        \tag{Q.residual}
\]
From (F.fracsimple), \(L^2<2\), and \(\mathcal D(u)\ge64u/225\),
\[
 c_{\rm FM}(W)>\frac{64}{2250\cdot101^3}
                    W^3(57/50)^{-m}.
                                                        \tag{Q.newbound}
\]
The bound \(L^2<2\) follows from
\((25/18)^2<2\). Dividing by (Q.oldbound), and writing
\(\beta_f=57/50\), gives
\[
 \begin{split}
 \frac{c_{\rm FM}(W)}{c_{\rm MV}(W)}
 &>\frac{W^2}{1280\cdot101^3\beta_f}
      \left(\frac{8/7}{\beta_f^{101/100}}\right)^n\\
 &>2^{n/1000-2a-31}>2.
 \end{split}                                        \tag{Q.paid}
\]
The middle inequality is exactly the pair of rational inequalities
\[
 (8/7)^{1000}>2\beta_f^{1010},\qquad
 1280\cdot101^3\beta_f<2^{31},                       \tag{Q.ratechecks}
\]
and the last is (Q.largeconductor). Each inequality is verified by integer
cross-multiplication in the finite driver. Unlike an interpolation
heuristic, the strict exponential separation compensates for the extra \(W\)
and the fixed displacement of the chosen coarse level.

The auxiliary first positive level can be eliminated from the comparison.
For every \(0<W\le2^{-4096}\), with \(a=\log_2(1/W)\), we obtain
\[
 \boxed{\frac{c_{\rm FM}(W)}{c_{\rm MV}(W)}
 >2^{\,2^{(a-9)/95}/1000-2a-31}>2.}                  \tag{Q.explicitgain}
\]
Indeed, substitute \(n>2^{(a-9)/95}\) from (Q.largeconductor)
into (Q.paid). The other inequality in (Q.largeconductor) gives
\(2^{(a-9)/95}/1000-2a-31>1\). This proves the stated strict
factor for the complete density formulas, with no new estimate or
choice of roots.

Combining (D.everyclock), (Q.paid) and (R.scoredomain) gives
\[
 \boxed{\forall c>c_0:\quad
 \underline d\{x:\tau_1(x)\le c\log x\}
       \ge c_{\rm FM}(W_*)>2c_{\rm MV}(W_*)>0.}
                                                        \tag{Q.headline}
\]
The explicit specialization \(c=10431/1000\) is included. With
\(c_*=c_{\rm FM}(W_*)\), (D.everyclock) proves (I.main), while
(Q.explicitgain) gives the stronger comparison (I.gain).
The bound uses (M.primitive), its
specified coefficient, the finite certificates and the auxiliary
estimates proved above. Both comparisons keep the root score and mixing estimate fixed.

### Improvement from the sixteen-step and complementary bounds

**Theorem (strict refinement at a fixed score).** For
\(0<W\le2^{-4096}\), with \(a=\log_2(1/W)\),
\[
 c_{\rm comp}(W)>c_{{\rm FM},16}(W)
                 >\frac{1369}{625}c_{\rm FM}(W),      \tag{Q.sixteengain}
\]
and
\[
 \frac{c_{{\rm FM},16}(W)}{c_{\rm FM}(W)}
       >2^{\,2^{(a-9)/95}/30-10}.                    \tag{Q.sixteenscoregain}
\]
All formulas have the same root score and mixing envelope.

*Proof.* Let \(m_*\) attain the positive maximum defining \(c_{\rm FM}(W)\).
By (Q.paid), its attaining branch is fractional. Write \(n=m_*+1=48t+r\),
\(0\le r<48\). Equation (Q.largeconductor) gives \(t\ge5\).
Every fractional remainder is at least one, and all rows are at most
\(b_{16}\); hence
\[
 D_n^{(3/2)}\ge b_{12}^{4t},\qquad
 D_{16,n}^{(3/2)}\le b_{16}^{3t+3}.
\]
The exact scalar comparisons are
\[
 b_{12}^4>b_{16}^3,\qquad
 25b_{12}^{20}>37b_{16}^{18},\qquad
 b_{12}^{20}>16b_{16}^{15},\qquad b_{16}^6<256.
                                                        \tag{Q.sixteenguards}
\]
Writing \(R=b_{12}^4/b_{16}^3\), the first pair implies
\(D_n^{(3/2)}/D_{16,n}^{(3/2)}\ge R^t/b_{16}^3>37/25\).
The common residual and fan prefactor cancel, so
\(v_{16,m_*}>(37/25)^2v_{m_*}\). Increasing convexity of
\(\mathcal D\), with \(\mathcal D(0)=0\), proves the factor
\(1369/625\) after optimizing.

For the stronger estimate, the last pair gives \(R^5>16\) and
\[
 (D_n^{(3/2)}/D_{16,n}^{(3/2)})^2
   \ge R^{2t}/b_{16}^6
   >2^{(8/5)t-8}>2^{n/30-10},
\]
since \(t\ge(n-47)/48\) and \(47/30+8<10\).
Use \(n>2^{(a-9)/95}\) and the same density conversion.

Finally, a maximizing branch of \(c_{{\rm FM},16}\) is also
fractional: \(c_{{\rm FM},16}\ge c_{\rm FM}>c_{\rm MV}\)
excludes both nonfractional branches. At that level the positive
complementary term makes \(\widetilde v_m\) strictly larger than
both occupied-only fractional bounds, since it uses
\(\mathcal B_m^{\rm best}\). Monotonicity of \(\mathcal D\)
proves \(c_{\rm comp}>c_{{\rm FM},16}\). All masses remain in
(D.domain). \(\square\)

### How a larger root score improves the full formula

**Theorem (cubic score comparison).** For the fixed retained envelope
and finite tables, if
\(0<W_1\le2^{-4096}\) and \(W_1<W_2\le W_{\max}\), then
\[
 c_{\rm FM}(W_2)>
       (W_2/W_1)^3c_{\rm FM}(W_1).                  \tag{Q.cubicscore}
\]

*Proof.* The positive maximum at \(W_1\) is attained. By (Q.paid),
no benchmark branch can attain it, so at a maximizing level \(m\),
\(c_{\rm FM}(W_1)=\mathcal D(v_m(W_1))\) with \(v_m(W_1)>0\).
Put \(a=W_2/W_1>1\), \(\delta=\kappa\epsilon_m\). Then
\(W_2-\delta=a(W_1-\delta)+(a-1)\delta\ge a(W_1-\delta)\);
hence \(v_m(W_2)\ge a^3v_m(W_1)\).
Strict convexity, monotonicity and \(\mathcal D(0)=0\) give
\(\mathcal D(a^3u)>a^3\mathcal D(u)\) for \(u>0\).
Maximizing at \(W_2\) proves the claim. All intermediate masses are at
most \(v_m(W_2)\), already in (D.domain). \(\square\)

The small-score hypothesis is used at the smaller score to prove which
branch attains the maximum. Merely including a cubic branch would not
suffice. The inequality is a lower comparison between certified formulas;
it gives neither their exact ratio nor an upper bound on that ratio.
The same argument for a globally active order-\(s\) branch gives exponent
\(s/(s-1)\), provided its dominance is separately proved.
For \(c_{{\rm FM},16}\), such dominance follows from
\(c_{{\rm FM},16}\ge c_{\rm FM}>c_{\rm MV}\) at the smaller
score. A maximizing branch is one of the two pure fractional branches,
whose denominator depends only on its level. The identical proof gives
\[
 c_{{\rm FM},16}(W_2)>
       (W_2/W_1)^3c_{{\rm FM},16}(W_1).              \tag{Q.sixteencubic}
\]
The denominator of \(\widetilde v_m\) also depends on the residual;
no cubic score comparison for \(c_{\rm comp}\) follows from this
argument. The pure-fractional comparisons remain available as lower
bounds through the retained formulas.


Appendix C supplies the available scores
\(W_{\mathcal F}^{\rm joint}>\mathfrak A_bW_*>E_bW_*>0\), all below
\(2^{-4096}\). Therefore (D.finitepool), with target one, and
(Q.cubicscore) give a strictly stronger common-density bound than the
baseline (Q.headline). The explicit comparisons are stated in
(C.densitygain). The meaning of \(W_*\) is unchanged.

### Finite level search

Each density formula can be approximated effectively. Once a positive rational incumbent for the mass maximum has
been certified, a finite level cutoff follows from the decreasing
tail bound, valid for \(m\ge32\),
\[
 u_m(W)\le
 64W^2(7/8)^m+\tfrac32W(2/3)^m
       +4W^3b_{12}^{-2\lfloor(m+1)/12\rfloor}.
                                                        \tag{Q.searchtail}
\]
The first two terms were proved above without the additional assumption
\(m\ge n\). For the third, all \(b_r\ge1\) and the squared fan
prefactor exceeds \(1/4\): indeed
\((512/81)/(9+4\sqrt2)>512/1215>1/4\).
Also \(L^2>1\). This gives the stated tail, which tends to zero
and can be bounded by exact rational arithmetic when \(W\) is rational.
The actual \(W_*\) is rational by (R.greedy) and the finite rational
startup recipe. A rational positive incumbent exists, for example by
using \(\epsilon_m\le C_6m^{-A}\) at a sufficiently large explicit
\(m\) and certified logarithm bounds. Compact-width minimization on
a fixed bounded interval uses continuous elementary functions with
computable uniform error bounds. The remaining finite maximum can therefore be approximated to any
prescribed accuracy, using certified enclosures for its finitely many
values.

For the refined formulas, a tail valid for \(m\ge32\) is
\[
 \begin{aligned}
 u_m^{\rm comp}(W)\le{}&64W^2(7/8)^m+\tfrac32W(2/3)^m\\
 &+16W^3\bigl(b_{12}^{-2\lfloor(m+1)/12\rfloor}
                +b_{16}^{-2\lfloor(m+1)/16\rfloor}\bigr).
 \end{aligned}                                        \tag{Q.refinedtail}
\]
Indeed both fractional fan ceilings exceed \(2\mu^{3/2}\) there:
the common prefactor exceeds \(1/2\), every remainder is at least
one, and \(b_{12}^2,b_{16}^2>4\). Thus
\(\widetilde v_m\le4\max\{v_m,v_{16,m}\}\).
The argument for the third term of (Q.searchtail) applies to each
fractional block length. This proves the displayed tail and finite
search for both new optimizers. Their expressions are continuous at
zero residual by their common bound \(p_m/\mu\), so equality decisions
at a zero residual are unnecessary for approximation to a requested
accuracy.

### The absolute scale of the density formulas

**Proposition (score-to-density scale).** Put \(a=\log_2(1/W)\) for
\(0<W\le2^{-4096}\), and define
\[
 m_+(W)=\max\{2,\lceil(3C_6/W)^{25/2314}\rceil\}.
\]
Then
\[
 \frac{4W}{25\,2^{m_+(W)}}\le c_{\rm FM}(W)
 \le47W\,2^{-\,2^{(a-9)/95}/6}.                    \tag{Q.formulascale}
\]

*Proof.* The first positive level \(n\) of (Q.firstpositive)
satisfies \(n>2^{(a-9)/95}>32\). In (Q.searchtail), use
\(b_{12}>2\), \((8/7)^6>2\), \((3/2)^6>2\), and
\(\lfloor(m+1)/12\rfloor\ge(m-11)/12\).
Its three terms are respectively at most
\(64W^2\,2^{-m/6}\), \((3/2)W\,2^{-m/6}\), and
\(16W^3\,2^{-m/6}\), since \(2^{11/6}<4\).
As \(W<1\), their sum is at most \((163/2)W\,2^{-m/6}\).
The recipe vanishes below \(n\); on its radial domain
\(\mathcal D(u)\le(128/225)u\). Maximizing and using
\((128/225)(163/2)=10432/225<47\) proves the upper bound.

At \(m=m_+(W)\), (M.envelope) gives
\(\epsilon_m\le C_6m^{-2314/25}\le W/3\).
Since \(\kappa<5/4\), the resulting error is less than \(W/2\).
The maximum branch has \(S_m\le(8/9)2^m\); its inverse and
\(\mathcal D(u)\ge64u/225\) give the lower bound, exactly as in
(D.elementarydensity). \(\square\)

These bounds concern the chosen formula. The error-envelope floor used
for the upper bound is not a lower bound on true mixing error.
For fixed \(C_6\) and tables, as \(W\downarrow0\), they imply
\[
 \frac a{95}-O(1)
 \le\log_2\log_2(1/c_{\rm FM}(W))
 \le\frac{25a}{2314}+O_{C_6}(1).                    \tag{Q.logscale}
\]
For fixed \(H,P>0\), (R.scorelower)--(R.scoreupper) give
\(W(q,P)=2^{-\Theta(3^q)}\) as \(q\to\infty\).
Multiplying by the fixed \(\mathfrak A_b\) retains this score scale;
composition with (Q.formulascale) gives
\(c_{\rm FM}(\mathfrak A_bW(q,P))=2^{-\,2^{\Theta(3^q)}}\).
This describes the formulas at fixed parameters as the residue level grows.
The canonical level satisfies the domain bound (C.domainguard).

The upper bound in (Q.formulascale) retains its literal twelve-step
meaning. For the strongest retained formula, a separate estimate is
\[
 c_{\rm comp}(W)<
 55W\,2^{-\frac18\,2^{(a-9)/95}}
 \qquad(0<W\le2^{-4096},\ a=\log_2(1/W)).            \tag{Q.refinedscale}
\]
To verify it, the rational rows satisfy
\(b_{12}^2>(11/10)^{12}\), \(b_{16}^2>(11/10)^{16}\), and
\(b_{12}^2,b_{16}^2<6\). For either block length \(d=12,16\),
\[
 b_d^{-2\lfloor(m+1)/d\rfloor}
 \le b_d^2(10/11)^{m+1}<6(10/11)^m.
\]
Hence each pure fractional mass is at most
\(24W^3(10/11)^m\), and the complementary one at most
\(96W^3(10/11)^m\) for \(m\ge32\). The two nonfractional
branches are bounded by \(64W^2(7/8)^m\) and
\((3/2)W(2/3)^m\), so their maximum together with the complementary
branch is at most \(96W(10/11)^m\), since \(W<1\).
All branches vanish below the first positive level \(n\).
Use \(\mathcal D(u)\le(128/225)u\),
\((128/225)96<55\), \((11/10)^8>2\), and
\(n>2^{(a-9)/95}\). This proves (Q.refinedscale).
The lower bound in (Q.formulascale) remains valid by inclusion of the
old formula. Thus the two-sided logarithmic scale in (Q.logscale)
also holds for \(c_{{\rm FM},16}\) and \(c_{\rm comp}\), with
their own constants. These upper bounds concern the defined density formulas.

### Comparison with Mazur's printed bound

With \(L_3(x)=\log_2\log_2\log_2 x\), (E.coefficientcomparison) gives
\(L_3(C_{\rm primitive})<176\) and
\(L_3(C_{\rm primitive}^{\rm Maz})>2^{172}\).
[Appendix B](#appendix_provenance) proves that this coefficient decrease
strictly improves the baseline density formula, accounting for both startup
rounding and score allocation.

We compare the actual arithmetic recipes, retaining the root parameters
printed in [3]. The printed primitive coefficient remains
\(C_{\rm primitive}^{\rm Maz}\), while ours is the smaller local coefficient
in (M.canonicalC). The printed sixth-order adapter is \(C_{\rm Maz}\) from
(M.sourceadapter), while our proved adapter is \(C_6=2D+2<C_{\rm Maz}\).
To preserve the literal printed benchmark, write
\[
 F_{b,{\rm Maz}}=2^{467}b16^b(C_{\rm Maz}+1).
\]
The marker normalization contributes the single factor \(2/3\) in
(M.marker); it is not absorbed into either coefficient.

Write \(b_{\rm Maz}=2^{80}\), \(H_{\rm Maz}=2b_{\rm Maz}+1\), and
\[
 t_{\rm Maz}=\lceil\log_2F_{b_{\rm Maz},{\rm Maz}}\rceil,\qquad
 N_{\rm Maz}=20000(t_{\rm Maz}+64),
\]
Starting from
\(\beta_0=b_{\rm Maz}\), let
\(\beta_{j+1}=\beta_j+\lfloor\beta_j/100\rfloor\) and
\[
 q_{\rm Maz}=\sum_{j<N_{\rm Maz}}
       \bigl(\beta_j+\lfloor3\beta_j/5\rfloor\bigr)
                     +\lfloor\beta_{N_{\rm Maz}}/4\rfloor.
\]
These expand the recurrences in [3, equations (8.1)--(8.4)].
Its printed constant in equations (8.5)--(8.6) is
\[
 \mathcal M=4^{H_{\rm Maz}+3^{q_{\rm Maz}}},\qquad
 m_{\rm Maz}=\left\lfloor(88\mathcal M C_{\rm Maz})^{1/6}\right\rfloor+1,
 \qquad c_{\rm Maz}=\frac3{256\mathcal M2^{m_{\rm Maz}}}.
                                                        \tag{Q.mazrecipe}
\]

**Proposition (comparison with the printed constant).** The selected score
satisfies
\[
 W_*>\mathcal M^{-1},\qquad
 c_{\rm MV}(W_*)>\frac{22208}{825}c_{\rm Maz},\qquad
 c_{\rm FM}(W_*)>\frac{44416}{825}c_{\rm Maz}.         \tag{Q.mazgain}
\]

*Proof.* Our construction starts at \(b=2^{25}\), with
\(t=\lceil\log_2F_b\rceil\), \(N\le4t/5\), \(q=q_N\),
and \(H=2b+1\). Since \(F_{b,{\rm Maz}}>F_b\) and these formulas increase with \(b\),
\(t_{\rm Maz}\ge t\) and \(N_{\rm Maz}>N\). The floor recurrence,
the summands in (B.conductor), and the terminal quarter are nondecreasing
in their initial value. The extra positive summand gives
\(q_{\rm Maz}\ge q+1\); also \(H_{\rm Maz}>H\).

By (R.scorelower), (R.denominator), and (R.conductorguards),
\[
 \begin{split}
 \log_2(W_*\mathcal M)
 &>3-1575N-6305+q\log_2 3
             +2(H_{\rm Maz}-H)+2(3^{q_{\rm Maz}}-3^q)\\
 &>4\cdot3^q-q-6302>0.
 \end{split}
\]
Here \(q\ge bN\ge1575N\). The final expression is already positive
at nine and increases thereafter, whereas our levels exceed nine.
This proves the first assertion.

Set \(m=m_{\rm Maz}\ge2\). The chosen envelope (M.envelope), with
exponent \(2314/25>6\), gives
\[
 \epsilon_m\le C_6m^{-6}<C_{\rm Maz}m^{-6}<\frac1{88\mathcal M},\qquad
 p_m>\frac{347}{352\mathcal M},
\]
using \(\kappa<5/4\) and \(W_*>\mathcal M^{-1}\).
Since \(S_m\le(8/9)2^m\) and
\(\mathcal D(u)\ge64u/225\),
\[
 c_{\rm MV}(W_*)\ge\mathcal D(p_m/S_m)
 \ge\frac8{25}p_m2^{-m}
 >\frac{347}{1100\mathcal M2^m}
 =\frac{22208}{825}c_{\rm Maz}.
\]
The radial domain is (D.domain). Finally (Q.paid), applied to
\(W_*\) using (R.scoredomain), gives the last assertion. \(\square\)

Retaining the symbolic score in the same calculation gives a stronger
comparison. Put \(R=W_*\mathcal M\) and
\(E_q=4\cdot3^q-q-6302\). The proof above gives
\(R>2^{E_q}>1\) and, at \(m=m_{\rm Maz}\),
\(p_m>(R-5/352)/\mathcal M\). Therefore
\[
 \frac{c_{\rm MV}(W_*)}{c_{\rm Maz}}
       >\frac{2048}{75}\left(R-\frac5{352}\right),\qquad
 \frac{c_{\rm FM}(W_*)}{c_{\rm Maz}}
       >\frac{4096}{75}\left(R-\frac5{352}\right).
                                                        \tag{Q.mazsymbolic}
\]
The first bound uses \((8/25)/(3/256)=2048/75\); the second
uses the certified factor greater than two at the same \(W_*\).
Substituting \(2^{E_q}\) for \(R\) preserves strict lower bounds.
The comparison is symbolic in the score and conductor.

Thus the conservative factor over the printed constant is
\(44416/825\approx53.8376\). Against the benchmark obtained by
doubling that constant through dyadic closure, the factor is
\(22208/825\approx26.9188\). The explicit numerical clock specialization here
is \(10431/1000=10.431\), compared with \(523/50=10.46\) in [3];
both count ordinary Collatz steps and use natural logarithms.

This printed benchmark is distinct from \(c_{\rm MV}(W)\), which fixes
our root family and optimizes the maximum and second-moment estimates.
The former comparison measures the change from the stated earlier bound;
the latter isolates the direct fractional-moment gain.
The benchmark [3] also includes a single explicit finite-cutoff recipe.
Here the proof gives effective eventual thresholds for every strictly
smaller density
constant, without assembling them into a comparable final cutoff formula.

### Further quantitative improvements

The convex-order inequality (F.convexfan) and optimal allocation formula
(D.hinge) in [Appendix D](#appendix_reference_consequences) identify a
further route: certify upper-tail profiles,
then compare the resulting density bound with the complete
\(c_{\rm comp}(W_*)\), keeping the roots and mixing envelope fixed.
The challenge is to propagate the finite distributions efficiently while
preserving certified upper bounds and to control the remaining level search.
A quantitative comparison can use the exact two-sided inverse
(D.twosidedcapacity) as well as propagated profile bounds.

Other direct moment orders can be used in (D.generalp). Interpolating
existing moment ceilings is insufficient on its own. Indeed, suppose
\(1<s_0<s_1\), \(0\le\alpha\le1\),
\(s=\alpha s_0+(1-\alpha)s_1\), and the only new bound is
\(B_s=B_{s_0}^{\alpha}B_{s_1}^{1-\alpha}\).
For a positive residual \(p\), let
\(v_s=p^{s/(s-1)}/(LB_s)^{1/(s-1)}\).
Its logarithm is the weighted average of \(\log v_{s_0}\) and
\(\log v_{s_1}\), with weights
\(\alpha(s_0-1)/(s-1)\) and \((1-\alpha)(s_1-1)/(s-1)\).
Thus it cannot exceed the better endpoint branch. New direct certificates
or additional distribution information are needed. The rate statement (F.divergencerate) does not by itself improve the
capacity formula as the order decreases. For exact fan moments and
residual \(p>0\), its full logarithm is
\[
 \log v_s=\frac{s}{s-1}\log(p/\mu)
       -\frac{\log L}{s-1}-D_s(H_m/\mu),
\]
where \(D_s(h)=\log\langle h^s\rangle_m/(s-1)\) for a
mean-one density \(h\). The residual and capacity terms remain in this formula alongside the
divergence. Adding a certified branch to the maximum
can never decrease the bound; a strict gain still needs proof against the
whole optimized formula. Polynomial or subexponential collision and
fractional-moment bounds remain open.

Absolute density also depends on the root score. From (D.domain),
\[
 c_{\rm FM}(W)\le
 \frac{32}{225}\left(e^{9W/4}-1\right)
 \sim\frac8{25}W\quad(W\downarrow0).                 \tag{Q.scoreceiling}
\]
This bounds the certified formula, not the true convergence density.
Even the exact residue-capacity optimum satisfies
\(\mathcal C_m(p_m)\le W/\mu\), by the feasible uniform allocation in
(D.hinge). Thus a substantial absolute lower bound requires improving
the root score or using further constraints on the actual sources, in
addition to improving concentration estimates.

A separate analytic route concerns the head localization in Section 6.
With the present squared-width loss, its two competing exponents are
\[
 a(v)=6407-\tfrac12(\log2)v^2,\qquad
 q_v-1=(\log2)v-1.                                  \tag{Q.headtradeoff}
\]
The first decreases and the second increases with \(v>0\).
Their equality determines the best asymptotic exponent within this
specific tradeoff; \(v_*=6749/50\) gives the retained exponent \(2314/25\)
with explicit rational slack. Improving the quadratic localization loss,
or replacing that argument by a multiscale or exponential-moment estimate,
could improve the resulting exponent. Such a change must reprove the
head-frequency estimate, rejection bound, level induction and complete
envelope with explicit constants.

The parameterized clock is established in (N.everyclock)--(D.everyclock),
with the full fixed density bound for every \(c>3/\log(4/3)\).
The endpoint clock remains unproved. A family of bounds valid for every
strictly larger coefficient does not imply the endpoint, and the
reference-model mean does not establish deterministic optimality below it.

## Appendix A. Comparison of fixed-depth and first-crossing seeds {#appendix_fixed_budget}

This appendix compares the fixed-depth seed with a central first-crossing
benchmark. The constants of both constructions are specified below.
Throughout this appendix \(b=2^{25}\),
the sequence \(b_j\) and the root index origin \(H=2b+1\) are fixed.
The following comparison is uniform in a fixed integer primitive coefficient
\(C\ge1\). Put \(D=C20^{6409}\); use the same \(C\) in both seed recipes.
The canonical instance takes \(C=C_{\rm primitive}\). The comparison with [3] takes \(C=C_{\rm primitive}^{\rm Maz}\). Each comparison uses one common value of \(C\). In this appendix
\(W_*\) denotes the fixed-depth score at that coefficient; it agrees with
(R.score) in the canonical instance.

### The two seed recipes

Use \(+\) for the fixed-depth seed and its local adapter, and \(-\)
for the first-crossing benchmark:
\[
 C_6^+=2D+2,\qquad C_6^-=2D+2+2^{481}=:C_{\rm fc}(C),
\]
\[
 q^+(n)=\sum_{j<n}b_j+\lfloor b_n/4\rfloor,\qquad
 q^-(n)=\sum_{j<n}(b_j+\lfloor3b_j/5\rfloor)+\lfloor b_n/4\rfloor.
                                                               \tag{Q.seedrecipes}
\]
The level \(q_n\) in (B.conductor) is \(q^+(n)\). The first-crossing
survival certificate uses
\(\Pi^-=C_{\rm fc,surv}/2^{1024}\), with the literal integer \(C_{\rm fc,surv}\):

```text
20617628314526275611176215079302618796161541826143958813539212954061565810783736808553005094090229880155492984737918050925474012626755862828385841557826047063282191704522378342863853189519310456714109487194639513012960066163451504920988540481985
```

Direct integer comparison gives
\[
 3\,2^{-214}<\Pi^-<\frac14<\Pi^+:=\frac{24}{25}.       \tag{Q.oldsurvival}
\]
This integer belongs to the first-crossing survival certificate. The
fixed-depth survival proof (R.certificate) does not use that computation.

Set \(F_b^\pm=2^{467}b16^b(C_6^\pm+1)\) and
\(t^\pm=\lceil\log_2F_b^\pm\rceil\). These rounded exponents agree exactly.
The common \(C\) is an integer, so
\(2D\) is divisible by \(2^{12819}\). Both \(2D+3\) and
\(2D+3+2^{481}\) lie strictly between \(2D\) and \(2D+2^{12819}\).
There is no power of two in this interval: any such power would exceed
\(2D\ge2^{12819}\) and would itself be divisible by \(2^{12819}\).
Multiplication by \(2^{467}b16^b\), a power of two at \(b=2^{25}\),
preserves the equality of the ceiling logarithms. Hence
\[
 t^+=t^-=t,\qquad V^+(n)=V^-(n)=V(n),\qquad
 L_t=\lceil\log_2(t+1)\rceil.                \tag{Q.roundinginvariance}
\]
The retained conservative variation majorant is the same for this
comparison; its separate optimization has not been used.

Define the first-crossing startup and scores by
\[
 N^-=\min\{n\ge16:V(n)<\Pi^-\},\qquad
 P^-=\Pi^--V(N^-),\qquad W_{\rm fc}=W(q^-(N^-),P^-),
\]
\[
 N^-_{\rm fixed}=\lceil100(t+3L_t+214)/131\rceil=N_{\rm fixed},
 \qquad
 W_{{\rm fixed,fc}}=
 W(q^-(N^-_{\rm fixed}),\Pi^--2^{-213}).              \tag{Q.previousscore}
\]
These scores use the first-crossing level and survival constant;
\(W_{{\rm fixed,fc}}\) also fixes the residual budget in advance.
Both scores are positive:
(R.searchendpoint)'s first three bounds put
\(V(N^-_{\rm fixed}-1)<3\,2^{-214}<\Pi^-\).
The same term-ratio argument also gives
\[
 V(N^-_{\rm fixed})<\tfrac12 V(N^-_{\rm fixed}-1)
    <\frac{32}{25}2^{-214}<2^{-213}.                 \tag{Q.previousadmissible}
\]
Thus the fixed-budget allocation is admissible.

### Level reduction and earlier startup

At every \(n\ge16\),
\[
 q^+(n)<\frac{63}{100}q^-(n).                        \tag{Q.conductortrim}
\]
To prove it, set \(S=\sum_{j<n}b_j\) and \(a_n=\lfloor b_n/4\rfloor\).
The recurrence gives \(b_n\le b+S/100\), while \(S\ge nb\), so
\(a_n/S\le1/(4n)+1/400\le29/1600\).
Also
\[
 \sum_{j<n}\lfloor3b_j/5\rfloor
 \ge\left(\frac35-\frac4{5b}\right)S.
\]
Since \((1+x)/(1+\delta+x)\) increases in \(x\) for \(\delta>0\),
\[
 \frac{q^+(n)}{q^-(n)}
 \le\frac{1+29/1600}{8/5-4/(5b)+29/1600}<\frac{63}{100};
\]
the last inequality is rational at \(b=2^{25}\). This is a reduction
greater than 37 percent at a common stage. Moreover
\(b_n=b+S/100+O(n)\) and \(n=o(b_n)\), by geometric growth, so
the same-stage ratio tends to \(401/641\).

Write \(N^+=N\) for the fixed-depth startup. The tail at 16 exceeds one after
multiplication by \(2^t\), so \(N^-\ge17\). For \(n\ge1\),
\[
 T_3(n-1,\lambda)
 =\lambda^{-1}\sum_{k\ge n}k^3\lambda^k
 <\lambda^{-1}T_3(n,\lambda).
\]
Together with \(\lambda^{-1}<5/2\) and (Q.oldsurvival), this gives
\[
 V(N^--1)<(5/2)\Pi^-<5/8<24/25,\qquad N^+<N^-.
                                                               \tag{Q.earlierseed}
\]
In particular \(q^+(N^+)<(63/100)q^-(N^-)\) as well.

The fixed-depth startup bound (R.startupoptimum), evaluated at \(n=N^-\)
and \(p=P^-\), followed by (R.conductormonotone), gives
\[
 W_*>2^{12193}W(q^+(N^-),P^-)>2^{12193}W_{\rm fc}.
                                                               \tag{Q.seedscoregain}
\]
The corresponding fixed-budget comparison follows from the same allocation
estimates. In the following denominator, \(a,d\)
are the rate integers of (R.variationdata). The positive rational
\(\Pi^--V(N^-)\) has denominator dividing
\(2^{1024}d^{N^-}(d-a)^4\), and so exceeds
\(2^{-1575N^--7324}\). The bounds
\(q^-(n)\ge bn\), \(H\le8q^-(n)+7\) and
\(q^-(n+1)\ge q^-(n)+1\) also hold. Apply the proof of
(R.startupoptimum) with \(q^-\), \(N^-\) and that denominator bound.
Since \(N^-<N^-_{\rm fixed}\), it proves
\[
 W_{\rm fc}>2^{12193}W_{{\rm fixed,fc}},\qquad
 W_*>2^{24386}W_{{\rm fixed,fc}}.                  \tag{Q.historicalscoregain}
\]

### Passing the gains to the complete density formulas

Here \(L=2\log2\) is the density interval length, distinct from \(L_t\).
For fixed \(m\), the function used in (D.inverse) is increasing and
concave on \([0,L/2]\), and its inverse is increasing and convex.
Consequently the maximum branch, the centered second-moment branch and
the direct fractional-moment branch are convex in \(W\); the last is
a positive multiple of a cubed positive part. Their maximum, its
composition with the increasing convex \(\mathcal D\), and the
supremum over levels remain convex. Both density formulas vanish at
zero. For either formula \(c\),
\[
 c(aW)\ge a\,c(W)
 \quad(a\ge1,\ 0\le W\le aW\le W_{\max}).             \tag{Q.scoregain}
\]
Let \(c_{{\rm FM},\pm}\) and \(c_{{\rm MV},\pm}\) denote the complete
formulas with adapter \(C_6^\pm\); all reference tables and the
compact-width terms \(E_v\) are identical. Thus
\(\epsilon_m^+\le\epsilon_m^-\) and each \(+\) formula dominates its
\(-\) counterpart at fixed score. Within this comparison, formulas without
subscripts are the \(+\) formulas at the chosen common \(C\); at the
canonical instance these are the main text's local formulas.

All scores above lie in \((0,2^{-4096})\), by (R.scoreupper) and their
large levels. The quantitative comparison (Q.paid) holds for either adapter:
its proof uses the same compact envelope and a coefficient at least one.
Applying (Q.scoregain) with the actual score ratios, (Q.seedscoregain)
and (Q.historicalscoregain) now gives
\[
 c_{\rm FM}(W_*)>
 2^{12193}c_{{\rm FM},-}(W_{\rm fc}),\qquad
 c_{\rm FM}(W_*)>
 2^{24387}c_{{\rm MV},-}(W_{{\rm fixed,fc}})>0.
                                                               \tag{Q.retainedgain}
\]
The second inequality includes the certified fractional-moment factor greater
than two. These inequalities hold separately at each common coefficient
\(C\). For the coefficient in [3], use
\(C=C_{\rm primitive}^{\rm Maz}\) throughout this appendix, then apply
(D.coefficientgain) to its left-hand current-seed formula. Thus the main
text's local formula also retains the displayed strict gains over those
specified first-crossing bounds. The rounding identity (Q.roundinginvariance)
is used at a common primitive coefficient.

## Appendix B. Dependence on the analytic coefficient {#appendix_provenance}

Fix the reference law, seed schedule, and finite moment tables. This appendix
compares the resulting startup, root score, and density bound as the valid
primitive-decay coefficient varies.

### Dependence on the analytic coefficient

Write \(t(C),V_C,N(C),P(C),W(C)\) for the fixed-depth startup and allocation of Section 8 with
integer primitive coefficient \(C\ge1\) and adapter \(2C20^{6409}+2\).
The seed, its survival probability, the rate \(\lambda\), and the level
sequence \(q(n)\) are fixed. The coefficient guards in Sections 6–8 hold
for every such \(C\). If \(C_1\le C_2\), then
\[
 t(C_1)\le t(C_2),\quad V_{C_1}(n)\le V_{C_2}(n),\quad
 N(C_1)\le N(C_2),\quad W(C_1)\ge W(C_2).            \tag{R.coefficientmonotonicity}
\]
Moreover \(t(C_1)<t(C_2)\) implies \(W(C_1)>W(C_2)\).

*Proof.* The first three comparisons follow from the increasing adapter,
the ceiling logarithm and the definition of the first positive residual.
If the startup indices agree, the smaller variation tail gives a larger
residual at that same level; use the strict increase in (R.greedy).
If \(N(C_1)<N(C_2)\), apply (R.startupoptimum) for \(C_1\) to the later
level \(N(C_2)\) and budget \(P(C_2)\le1\). Its proof is uniform in the
integer coefficient: (R.denominator) is unchanged because \(2^{t(C)}\)
is an integer. It gives even \(W(C_1)>2^{12193}W(C_2)\).
If the rounded exponents differ but startup indices agree, the residual
comparison is strict. \(\square\)

The arithmetic bounds (E.coefficientcomparison) give
\(C_{\rm primitive}^{\rm Maz}>4C_{\rm primitive}\). To see that the
factor four is allowed, (E.local-size) implies
\(L_3(4C_{\rm primitive})<177<2^{172}\).
Consequently the ratio of the corresponding \(F_b\)'s exceeds two, so
\(t(C_{\rm primitive}^{\rm Maz})\ge t(C_{\rm primitive})+1\). Thus
\[
 W_* = W(C_{\rm primitive})>
 W(C_{\rm primitive}^{\rm Maz})>0.                  \tag{R.localcoefficientgain}
\]
The comparison includes both the rounded startup and the resulting
allocation residual.

### Density bounds

**Corollary (coefficient improvement through the complete formula).**
For the same reference tables, let \(c_{{\rm FM},C}\) denote the density
formula with coefficient \(C\). If \(C_1\le C_2\) are valid integer
primitive coefficients, every term of the mixing envelope for \(C_1\)
is no larger than the corresponding term for \(C_2\). The maximum and
moment branches therefore give
\[
 c_{{\rm FM},C_1}(W)\ge c_{{\rm FM},C_2}(W)
 \quad(0\le W\le W_{\max}).
\]
The score scaling (Q.scoregain), whose proof uses only the defining
functions, then implies, with \(W_i=W(C_i)\),
\[
 c_{{\rm FM},C_1}(W_1)
 \ge \frac{W_1}{W_2}\,c_{{\rm FM},C_2}(W_2).
                                                               \tag{D.coefficientgain}
\]
Both scores are in the required small-score domain by (R.scoredomain).
For \(C_1=C_{\rm primitive}\), \(C_2=C_{\rm primitive}^{\rm Maz}\),
(R.localcoefficientgain) makes this a strict improvement of the baseline
density formula. The larger coefficient is also a valid primitive bound by (E.primitive)
and (E.coefficientcomparison). The other retained branches remain valid with
the new envelope, and every fixed-target source construction still fixes
its new startup, pool and score before choosing the clock.

## Appendix C. Proofs and certificates for the finite-root refinement {#appendix_roots}

This appendix proves the finite-root refinement (I.rootdensity).
The finite-pool theorem (D.finitepool) and the allocation comparison
(R.blockcomparison) reduce that task to residue coverage, separation of
root trajectories, and a lower bound for the combined score.
We verify these properties for valuation redistributions of certified
trajectories and evaluate their parameter counts exactly.

Section C.1 fixes the notation. Sections C.2–C.5 supply the constructions
and counting lemmas; Section C.6 assembles the score comparison.
Section C.7 gives the canonical finite certificates. The final two
sections explain a strict shared-allocation gain and the limitations of
increasing the number of blocks at fixed height. The baseline score
\(W_*\) and the density formulas in the main text retain their definitions.

### C.1. Setup and notation

In this appendix, a *seed* is a certified finite trajectory used to
construct additional roots. It is distinct from the fixed-depth word
family used for the initial marks in Sections 4 and 7.

The constructor (W.constructor) supplies each incoming block. We redistribute
valuations along certified finite trajectories while keeping complete
residue coverage and a finite root-to-one clock. Throughout this appendix,
\(b\ge2^{25}\), \(H=2b+1\), and the residue period and unit index set are
those of the root-pool section. All blocks use the same analytic inputs.

Let a seed have a certified first-hitting trajectory
\[
 y_0\xrightarrow{a_1}y_1\xrightarrow{a_2}\cdots\xrightarrow{a_D}1,
 \qquad 3y_{i-1}+1=2^{a_i}y_i,
\]
and let \(A_j=\sum_{i\le j}a_i\), \(A_0=0\). Fix \(e=e(y_0)\), \(d\ge0\), and
\[
 2^ey_0\equiv4^d\pmod9,\qquad
 \alpha_0=2^ey_0/4^d>3/4.
 \tag{C.seed}
\]
The finite base-height condition and the certified trajectory-height condition must also hold:
\[
 (2^ey_0\,4^{H-d}-1)/3\ge16^b,
 \qquad \max_j y_j<16^b,
 \qquad d\le H.
 \tag{C.baseheight}
\]
The base conditions imply \(T_0=2b-d+e-1\ge0\). Its only possible negative
case is \(e=1,d=H\), when the base root \((2y_0-1)/3<y_0<16^b\),
contradicting the height condition.


For a prefix of length \(r\), put
\[
 L_j^{(r)}=\frac{2^{A_r-A_j}y_r}{3^{r-j}},\quad
 \beta_r=\frac{2^e}{4^d}L_0^{(r)},\quad
 \Gamma_r=\frac{2^e}{4^d}\max_{0\le j<r}L_j^{(r)}.
 \tag{C.leading}
\]
The depth \(D\) and prefix length \(r\) below refer only to the
certified seed trajectory. They are unrelated to the reference moments
and divergence notation used elsewhere.

| Notation | Role in this appendix |
|---|---|
| \(y_0,\ldots,y_D=1;\ a_i,A_j\) | Certified seed trajectory, its valuations and their partial sums. |
| \(b,H=2b+1;\ e,d\) | Fixed height parameter, initial root index, and seed-dependent parameters in (C.seed). |
| \(r,\ell_i,S_j\) | Prefix length, added valuations and their partial sums in the general construction below. |
| \(Y_j,M_s\) | Modified trajectory states and the incoming root with index \(s\). |
| \(L_j^{(r)},\beta_r,\Gamma_r\) | Leading height coefficients defined in (C.leading); \(L_j^{(r)}\) is unrelated to the counting constant \(L\). |
| \(\chi_r,T_r\) | Height correction and remaining increment budget, defined in (C.heightdebit) and (C.budget). |
| \(N_r,Q_r,\Lambda_{y,r}\) | Rectangular count, quotient-simplex count and selected layer count, defined in (C.rectcount), (C.quotientcount) and (C.selectedcount). |
| \(E_b,\mathfrak A_b\) | Rectangular benchmark and canonical guaranteed score multiplier. |

### C.2. Rectangular redistribution and retained layers

The rectangular rule takes
\[
 t_i=3^{i+1}k_i,\quad h=\sum_it_i\le T_0:=2b-d+e-1,
\]
\[
 Y_r=y_r,\quad Y_{i-1}=\frac{2^{a_i+2t_i}Y_i-1}{3},\quad
 M_s=\frac{2^{2(s-d-h)+e}Y_0-1}{3}.
 \tag{C.rectangular}
\]
A sufficient rectangular condition is \(\Gamma_r<1\). It implies \(\beta_r<1\).

**Proof of its arithmetic interface.** The valuation identity
\(\nu_3(4^t-1)=1+\nu_3(t)\) gives \(4^{t_i}\equiv1\pmod{3^{i+2}}\). Backwards induction
gives \(Y_j\equiv y_j\pmod{3^{j+2}}\). In particular \(Y_0\equiv y_0\pmod9\), and \(h\)
is a multiple of nine, so the root's compensated affine coefficient is one modulo nine.
The original unit index set is therefore unchanged.

The geometric and clock arguments are the special case \(\ell_i=2t_i\) of the height and
clock lemmas below. Every new root is at least \(16^b\), all later odd states are below
\(16^b\), and its clock is \(2s+e+1+\tau_1(y_0)-2d\). A parameter vector is recovered
from its actual valuations. Across different seeds, distinct full first-hitting depths
are a sufficient distinctness certificate. \(\square\)

**Theorem C.1 (exact count recurrence).**

Set
\[
 N_r(T)=\#\{k\in\mathbb Z_{\ge0}^r:\sum_{i=1}^r3^{i+1}k_i\le T\},
\]
with \(N_r(T)=0\) for \(T<0\) and \(N_0(T)=1\) for \(T\ge0\). Then
\[
 \boxed{N_r(T)=N_{r-1}(T)+N_r(T-3^{r+1}).}
 \tag{C.rectcount}
\]
The number with last nonzero coordinate exactly \(r\) is
\[
 \Delta_r(T)=N_r(T-3^{r+1}).
 \tag{C.rectlayer}
\]

**Proof.** Partition by \(k_r=0\) or \(k_r>0\). In the second part subtract one from
\(k_r\); this is a bijection to the indicated lower-budget set. \(\square\)

For \(T\ge0\), the unit-cube bounds give
\[
 \frac{T^r}{r!\,3^{r(r+3)/2}}\le N_r(T)
 \le\frac{(T+\sum_{i=1}^r3^{i+1})^r}{r!\,3^{r(r+3)/2}}.
 \tag{C.volume}
\]
Flooring points of the real simplex proves the lower bound via unit cubes; its cube
cover lies inside the enlarged simplex for the upper bound. The resulting asymptotic is
for fixed \(r\), not uniformly growing dimension.

**Theorem C.2 (retention of sharper earlier layers).**

Unrolling the original prefix gives
\[
 L_0^{(r)}=y_0+\sum_{i=1}^r\frac{2^{A_{i-1}}}{3^i},
 \qquad
 \beta_{r+1}-\beta_r=\frac{2^{e+A_r}}{4^d3^{r+1}}>0.
 \tag{C.betastep}
\]
Thus replacing each retained block ceiling by the final \(\beta_r\) can weaken a coarse
certificate. Instead define
\[
 G_R(T)=\alpha_0^{-1}+\sum_{r=1}^R\frac{N_r(T-3^{r+1})}{\beta_r}.
 \tag{C.rectscore}
\]
Then
\[
 \boxed{G_R(T)-G_{R-1}(T)=N_R(T-3^{R+1})/\beta_R.}
 \tag{C.rectincrement}
\]
The right side is positive exactly when that new rectangular layer is nonempty.

**Proof.** The zero vector gives the base target block and the factor \(\alpha_0^{-1}\).
A nonzero vector has a unique last nonzero coordinate \(r\); its later coordinates
vanish, so the target is exactly its \(r\)-prefix construction, with coefficient less
than \(\beta_r\). Apply (R.blockcomparison) separately to those \(\Delta_r\) blocks and
retain their budgets. \(\square\)

Equation (C.rectincrement) gives the exact increment of the guaranteed
multiplier.

#### Exact evaluation without canonical root enumeration

The same counts admit the following exact radix evaluation. Let
\[
 H_{r,p}(n)=[z^n](1-z)^{-(p+1)}\prod_{j=0}^{r-1}(1-z^{3^j})^{-1}.
\]
Then \(N_r(T)=H_{r,0}(\lfloor T/9\rfloor)\), \(H_{0,p}(n)=\binom{n+p}{p}\), and all
values with \(n<0\) vanish. For \(n=3m+a\), \(a\in\{0,1,2\}\), define
\[
 c_j(p,a)=\sum_{v=0}^j(-1)^v\binom jv
                 \binom{-3(v+1)+a+p+1}{p+1}.
\]
Using generalized binomial coefficients for negative upper arguments,
\[
 H_{r,p}(3m+a)=\sum_{j=0}^{p+1}c_j(p,a)H_{r-1,j}(m).
 \tag{C.radix}
\]
To prove it, expand the polynomial \(\binom{3u+a+p+1}{p+1}\) in the basis
\(\binom{u+j}{j}\), whose coefficients are the displayed backward differences. Apply the
generating-function identity for division of the geometric weights by three. This is a
signed-integer recurrence; no decimal values decide the counts.

The canonical rectangular prefixes \((7,15,14)\) give
\[
 E_b=1+G_{101,7}(2b-4)+G_{193,15}(2b-4)+G_{12289,14}(2b-7).
 \tag{C.E}
\]
It remains a separately named benchmark in the canonical comparison below.

### C.3. General increments, heights, residues and clocks

Now allow **arbitrary nonnegative integer increments** \(\ell_1,\ldots,\ell_r\), not
necessarily even. Write
\[
 S=\sum_{i=1}^r\ell_i,\qquad S_j=\sum_{i=1}^j\ell_i.
\]
Define, whenever the divisions are integral,
\[
 Y_r=y_r,\qquad
 Y_{i-1}=\frac{2^{a_i+\ell_i}Y_i-1}{3},
 \tag{C.redistribution}
\]
and let the incoming root exponent be
\[
 a_{\rm in}(s)=2(s-d)+e-S,\qquad
 M_s=\frac{2^{a_{\rm in}(s)}Y_0-1}{3}.
 \tag{C.incoming}
\]
Here \(e\) is the original seed parameter. It need not equal \(e(Y_0)\). Correct
incoming parity will follow from the compensated congruence; one must not substitute a
nonintegral half-shift into the one-step constructor formula.

Assume the backward values are positive odd units and satisfy
\[
 2^eY_0\equiv4^d2^S\pmod9.
 \tag{C.compensated}
\]
The residue-completion theorem gives a complete deterministic way to meet these conditions.

**Lemma C.3 (geometry and exact affine coefficient).**

For \(0\le j<r\),
\[
 2^{S-S_j}y_j\le Y_j<L_j^{(r)}2^{S-S_j}.
 \tag{C.geometry}
\]
Consequently
\[
 \alpha(\ell)=\frac{2^eY_0}{4^d2^S},\qquad
 \alpha_0\le\alpha(\ell)<\beta_r,
 \qquad
 M_s=\alpha(\ell)R_s+\frac{\alpha(\ell)-1}{3}.
 \tag{C.affine}
\]
The exact subtraction terms are
\[
 \boxed{
 \alpha(\ell)=\beta_r-
 \frac{2^e}{4^d}
       \sum_{i=1}^r\frac{2^{A_{i-1}}}{3^i2^{\ell_i+\cdots+\ell_r}}.
 }
 \tag{C.exactalpha}
\]

**Proof.** Backwards induction proves the lower bound. If \(Y_i\ge2^{S-S_i}y_i\), then
\[
 Y_{i-1}\ge2^{S-S_{i-1}}y_{i-1}
                   +\frac{2^{S-S_{i-1}}-1}{3}
 \ge2^{S-S_{i-1}}y_{i-1}.
\]
Dropping the subtractive one in each inverse step proves the strict upper bound; already
the last inverse step is strictly below its leading term. Unrolling the complete affine
composition yields (C.exactalpha). Dividing (C.geometry) at \(j=0\) by the stated powers
gives (C.affine). \(\square\)

**Lemma C.4 (height correction).**

Assume \(\beta_r<1\). There is no need to impose \(\Gamma_r<1\). Define the least
nonnegative integer
\[
 \chi_r=\min\{v\ge0:\Gamma_r2^{e-2}\le4^v\},
 \qquad
 T_r=2b-d+e-1-\chi_r.
 \tag{C.heightdebit}
\]
Restrict the total increment by
\[
 S\le2T_r.
 \tag{C.budget}
\]
If \(T_r<0\), use no nonzero vectors at this layer. Under the base conditions
(C.seed)–(C.baseheight), every selected root is at least \(16^b\), every subsequent
modified odd state is strictly below \(16^b\), and the incoming exponent is positive.

**Proof.** At \(s\ge H\),
\[
 a_{\rm in}(s)\ge2H-2d+e-2T_r=4-e+2\chi_r\ge2.
\]
The lower bound \(\alpha\ge\alpha_0\) retains the finite minimum-root height condition. On
the other hand,
\[
 Y_j<L_j^{(r)}2^{2T_r}
 \le\Gamma_r2^{e-2}4^{-\chi_r}16^b
 \le16^b.
 \tag{C.height}
\]
The inequality is strict because the leading-term bound is strict. The unchanged tail
already lies below \(16^b\). \(\square\)

Thus a large intermediate leading coefficient costs a fixed number of budget units
rather than automatically prohibiting the prefix. Earlier layers keep their own
\(\chi_j,T_j,\beta_j\); a later height correction must not be imposed on them.

**Lemma C.5 (residues, distinctness, and clock).**

Under (C.compensated), the coefficient \(\alpha\) is one modulo nine in the
dyadic-rational sense. Therefore \(r\mapsto\alpha r+(\alpha-1)/3\) is an invertible
affine map modulo every \(3^q\), with constant term divisible by three. The baseline indices
\(\mathcal S_q\) give one root in every unit residue, unchanged.

For every selected vector,
\[
 \tau_1(Y_0)=\tau_1(y_0)+S,
 \qquad
 \boxed{\tau_1(M_s)=2s+e+1+\tau_1(y_0)-2d.}
 \tag{C.clock}
\]

**Proof.** Multiplying (C.compensated) by the inverse of \(4^d2^S\) proves the
coefficient congruence. The root-period lemma for \(R_s\), followed by the affine
permutation, gives complete coverage.

Oddness of each \(Y_i\) makes its valuation exactly \(a_i+\ell_i\). The lower geometry
bound implies \(Y_j\ge y_j>1\) for \(j<r\), so there is no premature hit of one. The
unchanged tail follows from \(Y_r=y_r\). Sum the ordinary step costs and cancel \(S\)
against the incoming exponent in (C.incoming). \(\square\)

Within one seed, the full vector of increments, padded by zeros to the original
first-hitting depth, is recovered from the actual valuation word. Different vectors give
different targets. To combine different seeds, require distinct perturbed targets;
distinct original full first-hitting depths are a sufficient certificate, used in the
canonical example. The height barrier then proves the joint root antichain, including
the unchanged baseline block.

### C.4. Residue completion

The necessary congruences can be solved backwards from the certified endpoint, with a
bounded correction at each step.

**Theorem C.6 (complete residue-completion algorithm).**

Fix a prefix of length \(r\ge1\), with base conditions (C.seed), and choose
\[
 (k_1,\ldots,k_r)\in\mathbb Z_{\ge0}^r,
 \qquad (\varepsilon_1,\ldots,\varepsilon_{r-1})\in\{1,2\}^{r-1}.
\]
The labels \(\varepsilon_i\) prescribe the unit residues of the intermediate states
\(Y_i\). They are deterministic branch labels, not probabilities.

Start with \(Y_r=y_r\). For \(i=r,r-1,\ldots,2\), choose the unique
\(c_i\in\{0,\ldots,5\}\) such that
\[
 2^{a_i+c_i}Y_i\equiv3\varepsilon_{i-1}+1\pmod9,
 \qquad
 \ell_i=6k_i+c_i,
 \qquad
 Y_{i-1}=\frac{2^{a_i+\ell_i}Y_i-1}{3}.
 \tag{C.internal}
\]
Put \(S'=\sum_{i=2}^r\ell_i\), with \(S'=0\) when \(r=1\), and form
\[
 D\equiv2^{e+a_1}Y_1-3\cdot4^d2^{S'}\pmod{27}.
 \tag{C.topresidue}
\]
Choose the unique \(c_1\in\{0,\ldots,17\}\) with
\[
 2^{c_1}D\equiv2^e\pmod{27},
 \qquad
 \ell_1=18k_1+c_1,
 \qquad
 Y_0=\frac{2^{a_1+\ell_1}Y_1-1}{3}.
 \tag{C.top}
\]
This always constructs positive odd unit states, exact valuations \(a_i+\ell_i\), and
the compensated congruence (C.compensated).

Moreover, the construction is a bijection onto the nonnegative increment vectors for
which all the backward states are positive odd units and (C.compensated) holds. No
coordinatewise condition \(3^{i+1}\mid\ell_i/2\) is required.

**Proof: internal steps.** Powers of two have order six modulo nine and enumerate all
its units. Since \(Y_i\) is a unit, exactly one exponent residue gives each of the two
target numerator residues \(4\) and \(7\). Division by three gives
\(Y_{i-1}\equiv\varepsilon_{i-1}\pmod3\). The quotient is integral and odd. Positivity
and the lower bound by the original state follow from the induction in Lemma C.3.

**Proof: first step and root condition.** The residue \(D\) is a unit modulo three and
hence modulo 27. Powers of two have order eighteen modulo 27 and enumerate all units:
\(2^9\equiv-1\pmod{27}\), while \(2^6\not\equiv1\pmod{27}\) and
\(2^2\not\equiv1\pmod{27}\), excluding the proper candidate orders after using the
nine-step sign. Thus (C.top) has exactly one residue solution.

Reducing (C.top) modulo three gives \(2^{a_1+\ell_1}Y_1\equiv1\pmod3\), so \(Y_0\) is
integral. In full precision it reads
\[
 2^e(2^{a_1+\ell_1}Y_1-1)
 \equiv3\cdot4^d2^{S'+\ell_1}\pmod{27}.
\]
Divide this congruence by three, using the integer numerator, to obtain
\[
 2^eY_0\equiv4^d2^S\pmod9.
\]
It also implies \(3\nmid Y_0\). Positive oddness follows as before.

**Proof: bijection.** Conversely, take any vector satisfying the stated physical and
congruence conditions. For \(i\ge2\), the residue of \(Y_{i-1}\) determines
\(\varepsilon_{i-1}\), and \(\ell_i\bmod6\) must be the unique solution of (C.internal).
Its quotient is \(k_i=\lfloor\ell_i/6\rfloor\). The final compensated congruence is
equivalent to (C.top), so \(\ell_1\bmod18\) is the unique first residue and
\(k_1=\lfloor\ell_1/18\rfloor\). These recovered inputs reproduce the vector. \(\square\)

For \(r=1\), one has \(D=2^e+3(2^ey_0-4^d)\equiv2^e\pmod{27}\), so the base congruence
makes \(c_1=0\). Thus \(\ell_1=18k_1\), exactly the original single-parameter lift. For
a general prefix,
\[
 S=18k_1+6\sum_{i=2}^rk_i+\sum_{i=1}^rc_i.
 \tag{C.totalincrement}
\]
The uniformly bounded residue corrections give the counting cost.

#### A small parity-changing example

Use the seed \(101\), with \(d=4,e=1\), and its first two valuations \((4,1)\), ending
at \(29\). Set \(k=(0,0)\) and choose \(Y_1\equiv2\pmod3\). The algorithm gives
\[
 (\ell_1,\ell_2)=(11,2),\qquad
 Y_1=77,\qquad Y_0=841045.
\]
Indeed
\[
 3\cdot841045+1=2^{15}\cdot77,\qquad
 3\cdot77+1=2^3\cdot29.
\]
The total added valuation is 13. The roots are
\[
 M_s=(841045\,2^{2s-20}-1)/3,
 \qquad \tau_1(M_s)=2s+19.
\]
For example, at \(b=5,H=11,s=11\), the root is \(1121393>16^5\), while all its
subsequent odd states are below \(16^5\). Its ordinary first hitting time is 41. This is
an arithmetic example only; the density theorem still retains its canonical analytic
range for \(b\).

Here \(e(Y_0)=2\), although the seed parameter is \(e=1\). The compensated incoming
exponent has automatically changed parity. Keeping \(e(Y_0)=e(y_0)\) would wrongly
exclude this valid family.

#### Relation to the rectangular family

Every rectangular vector satisfies the completed family's conditions: it is
integral, all intermediate states are units, and its affine coefficient is one modulo
nine. Theorem C.6 therefore recovers it uniquely. The completed family is strictly larger; the
example above contains an odd increment and cannot be a rectangular vector.

The original recurrence (C.rectcount) remains the exact count of its original
rectangular set. It must not be presented as the exact count of the larger
residue-completed set.

### C.5. Counting completed layers

**Lemma C.7 (quotient-simplex count).**

For \(r\ge1\), define
\[
 Q_r(n)=\#\{k\in\mathbb Z_{\ge0}^r:3k_1+k_2+\cdots+k_r\le n\},
 \qquad Q_r(n)=0\ (n<0).
\]
Then
\[
 \boxed{
 Q_r(n)=\sum_{v=0}^{\lfloor n/3\rfloor}
                  \binom{n-3v+r-1}{r-1}.
 }
 \tag{C.quotientcount}
\]
This counts all choices of the remaining \(r-1\) coordinates and unused budget after
choosing \(k_1=v\).

For an efficient exact evaluation, write \(n=3m+a\), \(a\in\{0,1,2\}\), and
\[
 P_{r,a}(u)=\binom{3u+a+r-1}{r-1},\qquad
 d_j=\sum_{v=0}^j(-1)^{j-v}\binom jvP_{r,a}(v).
\]
Then
\[
 \boxed{
 Q_r(3m+a)=\sum_{j=0}^{r-1}d_j\binom{m+1}{j+1}.
 }
 \tag{C.quotienteval}
\]

**Proof.** Reindex the sum in (C.quotientcount) as \(\sum_{u=0}^mP_{r,a}(u)\). The
polynomial has degree \(r-1\), so its finite Newton expansion is
\(P(u)=\sum_{j=0}^{r-1}d_j\binom uj\). Summing and using \(\sum_{u=0}^m\binom
uj=\binom{m+1}{j+1}\) proves (C.quotienteval). All arithmetic is integer arithmetic. \(\square\)

Thus the dimension-43 count is evaluated from a degree-42 polynomial
using exact binomial operations.

**Lemma C.8 (disjoint last-nonzero layers with explicit correction budgets).**

A nonzero increment vector has a unique last nonzero coordinate \(r\). Later coordinates
are zero, so it is the \(r\)-prefix construction. At its last internal step,
\(Y_r=y_r\). The two residue completions for \(c_r\) are
\[
 c_r=0\quad\text{or}\quad
 c_r=\sigma_r:=\begin{cases}
 2,&y_{r-1}\equiv1\pmod3,\\
 4,&y_{r-1}\equiv2\pmod3.
 \end{cases}
\]
The first choice preserves the original residue of \(y_{r-1}\), and the other switches it.

For \(r\ge2\), each of the earlier \(r-2\) internal residues is freely chosen from two
units. The first correction is at most 17, and those earlier internal corrections are at
most five each. Consequently a fixed last correction \(c\in\{0,\sigma_r\}\) has total
correction at most
\[
 \delta_{r,c}=17+5(r-2)+c=5r+7+c.
 \tag{C.correctionbudget}
\]

To ensure \(\ell_r>0\), use three disjoint classes:

| Class | Last residue correction | Last quotient | Earlier branch choices | Guaranteed free-quotient budget |
|---|---:|---:|---:|---|
| A | \(0\) | \(k_r\ge1\) | \(2^{r-2}\) | subtract \(\delta_{r,0}+6\) from \(2T\) |
| B | \(\sigma_r\) | \(k_r\ge1\) | \(2^{r-2}\) | subtract \(\delta_{r,\sigma_r}+6\) from \(2T\) |
| C | \(\sigma_r\) | \(k_r=0\) | \(2^{r-2}\) | subtract \(\delta_{r,\sigma_r}\) from \(2T\) |

Subtract one from \(k_r\) in A and B. In C omit the last quotient. The exact number in
the selected parameter classes is
\[
 \boxed{
 \begin{aligned}
 \Lambda_r(T)=2^{r-2}\bigg[&
 Q_r\!\left(\left\lfloor\frac{2T-\delta_{r,0}-6}{6}\right\rfloor\right)
 +Q_r\!\left(\left\lfloor\frac{2T-\delta_{r,\sigma_r}-6}{6}\right\rfloor\right)\\
 &+Q_{r-1}\!\left(\left\lfloor\frac{2T-\delta_{r,\sigma_r}}6\right\rfloor\right)
 \bigg]
 \quad(r\ge2),
 \end{aligned}}
 \tag{C.selectedcount}
\]
where \(\Lambda_r(T)=0\) for \(T<0\), and
\[
 \Lambda_1(T)=\max(0,\lfloor T/9\rfloor).
\]

**Proof.** The last-step residues follow by multiplying the original numerator residue,
either four or seven modulo nine, by powers of two. The alternate valid unit output
occurs at exponent two or four respectively. At this last step, \(c_r\) is independent
of its own quotient \(k_r\),
because \(2^6\equiv1\pmod9\). Earlier corrections may depend on downstream
quotients through the computed states; the uniform bounds cover that
dependence.

For each fixed earlier branch string, (C.totalincrement) and the correction budget
ensure \(S\le2T\). The quotient counts are precisely (C.quotientcount). Theorem C.6 is
injective in all the choices, and the three last-quotient/residue classes are disjoint.
Therefore multiplication by \(2^{r-2}\) and addition are exact counts of the chosen
parameter classes. At \(r=1\), the nonzero shifts are exactly \(18k_1\le2T\),
\(k_1\ge1\). \(\square\)

These are exact counts of **explicitly selected safe parameter sets**. They are lower
bounds on the count of all admissible completed vectors, because an individual vector
can have a smaller correction than the common budget used above. Neither rounding nor a
distributional assumption enters the selected counts.

#### The larger finite domain

For every prefix \(r\), let \(\mathscr L_r\) consist of all nonnegative vectors with
last nonzero coordinate \(r\), satisfying the physical unit conditions, (C.compensated),
and \(S\le2T_r\). This is a finite, deterministically decidable set. Theorem C.6
enumerates it by bounded quotient vectors and unit branches, followed by its literal
total-budget test. It contains the selected classes of Lemma C.8.

Padded zero suffixes identify these as disjoint layers of the full original certificate.
The single all-zero vector is added once per seed, not once for every prefix.

For a depth-\(D\) seed, all these choices inject into the unrestricted depth-\(D\)
completion parameters with
\(18k_1+6\sum_{i\ge2}k_i\le2T_0\). Thus the number of its blocks, including its zero
vector, is at most
\[
 2^{D-1}Q_D(\lfloor T_0/3\rfloor).
 \tag{C.blockcount}
\]
This upper bound deliberately ignores some completion and height costs. It is used only
for the domain condition.

#### Structural count improvement at fixed dimension

For fixed \(r\), let \(\mathcal N_r(T)\) count all completed vectors with \(S\le2T\),
before imposing a prefix-specific height correction. For \(r\ge2\), the last residue
correction is at most four, the first is at most seventeen, and the other corrections
total at most \(5(r-2)\). Thus
\[
 2^{r-1}Q_r\!\left(\left\lfloor\frac{2T-(5r+11)}6\right\rfloor\right)
 \le \mathcal N_r(T)
 \le2^{r-1}Q_r(\lfloor T/3\rfloor).
\]
The same quotient-simplex argument as for (C.volume), now with weights
\((3,1,\ldots,1)\), gives \(Q_r(n)=n^r/(3r!)+O_r(n^{r-1})\). Therefore
\[
 \mathcal N_r(T)=
 \frac{2^{r-1}}{3^{r+1}r!}T^r+O_r(T^{r-1}).
\]
For \(r=1\) and \(T\ge0\), the exact count is \(1+\lfloor T/9\rfloor\), with the same
leading coefficient. The selected last-layer formula (C.selectedcount) has this same
degree-\(r\) leading coefficient: the first two terms supply it, while the third and the
shorter layers have lower degree.

Relative to the rectangular lattice's degree-\(r\) coefficient in (C.volume), the ratio is
\[
 2^{r-1}3^{(r-1)(r+2)/2}.
\]
This asymptotic comparison holds with \(r\) fixed. The canonical
finite result uses the explicit counts and inequalities below.

#### Retained-layer multiplier for the completed construction

Define
\[
 \widehat G_R
 =\alpha_0^{-1}+\sum_{r=1}^R\frac{\Lambda_r(T_r)}{\beta_r}.
 \tag{C.layerscore}
\]
Then
\[
 \widehat G_R-\widehat G_{R-1}=\Lambda_R(T_R)/\beta_R\ge0.
\]
Every nonempty selected new layer gives a strictly positive increment. Crucially, a
later \(\beta_R\), height correction, or shorter budget never replaces the earlier layers'
retained certificates. This is the analogue of (C.rectincrement), with both
residue corrections and height bounds included.

Using the exact count of \(\mathscr L_r\), or finer per-vector coefficients from
(C.exactalpha), can improve this convenient explicit multiplier further. The
selected-set formula is not asserted to equal the exact shared score.

### C.6. Finite-family score comparison

**Theorem C.9 (residue-completed finite-family score comparison).**

Retain the analytic and counting inputs of the main text. Fix a nonempty finite
collection of certified convergent odd unit seeds \(y\), greater than one, each with
parameters \(e=e(y),d\) satisfying (C.seed)–(C.baseheight). For each seed choose a
terminal prefix length \(1\le R\le D\), where \(D\) is its certified first-hitting
depth, and assume \(\beta_R<1\). Earlier leading coefficients are smaller by
(C.betastep). Form \(\chi_r,T_r\) separately for every \(1\le r\le R\).

Use the zero vector once and any or all of the finite completed layers \(\mathscr L_r\).
In particular one may use the full layer sets. Require that generated targets from
different seeds be distinct; pairwise distinct full accelerated first-hitting depths
suffice. Retain the original block \(\{R_s:s\in\mathcal S_q\}\).

The finite score comparisons below hold for every \(q\ge2\).
For the persistent-mark and density conclusions, take \(q=q_N\) and
\(p=P\), as in (R.markapplication).
The resulting root family is a finite convergent antichain, partitioned into complete
unit-residue blocks; at \(q=q_N\) these blocks carry the common persistent
marks (G.marks). With the selected classes included, set
\[
 \mathfrak A=1+\sum_{\text{seeds }y}\widehat G_{R_y}.
\]
Then
\[
 \boxed{
 W_{\mathcal F}^{\rm joint}(q,P)>\mathfrak A\,W(q,P)>0.
 }
 \tag{C.master}
\]
All roots are at least \(16^b\), every later odd state from a new root is below
\(16^b\), the largest root is the largest baseline root, and every root clock is given by
(C.clock).

Let
\[
 J_{\rm up}=1+\sum_y2^{R_y-1}Q_{R_y}(\lfloor T_{0,y}/3\rfloor).
\]
The following bound holds:
\[
 W_{\mathcal F}^{\rm joint}
 <\frac43J_{\rm up}16^{-b}.
 \tag{C.domain}
\]
At \(q=q_N\), whenever the shared score is within \(W_{\max}\),
(D.finitepool) gives the corresponding every-clock density bound.
If the right side of (C.domain) is at most \(2^{-4096}\), all
positive scores in (C.master) are also in the cubic comparison range.

**Proof.** The geometric and residue lemmas prove each block's admissibility. A target's
modified first-hitting depth is unchanged, so the stated cross-seed condition proves
target distinctness. Within a seed, actual valuations recover the increment vector and
hence its unique layer. A root's next odd value identifies its block. The height barrier
proves no root subsequently visits any selected root. Therefore there is one aggregate
\(1/x\) bound on each source weight.

Every block uses the same capacity \(B_q\) and mass requirement \(K_qP\).
At \(q=q_N\), the mark identity, uniform over roots, and full variation bound supply
these as actual persistent marks in every complete block.
For the zero vector use the factor
\(\alpha_0^{-1}\). In layer \(r\), (C.affine) gives \(M_s<\beta_rR_s\), so
(R.blockcomparison) supplies a strict block factor \(\beta_r^{-1}\). Count the disjoint
selected classes by (C.selectedcount), sum their budgets, retain the baseline block, and
apply the shared-score dominance (R.jointdominance). This proves (C.master).

For (C.domain), the constant vector \(v_r=P\le1\) is feasible in (R.jointscore). Each
block obeys \(M_{s+1}=4M_s+1\) on the full sequence of consecutive indices and starts at
least at \(16^b\). Its finite unit-subset reciprocal sum is strictly less than
\(\sum_{j\ge0}4^{-j}16^{-b}=(4/3)16^{-b}\). Bound the number of blocks by (C.blockcount)
and include the baseline block. This proves an upper bound on the finite allocation minimum,
with no sum over infinitely many physical histories. The remaining density conclusion is (D.finitepool). \(\square\)

For a seed used only through a proper prefix, (C.blockcount) and (C.domain) use that
prefix length and pad shorter layers only to it. Distinctness still uses the full
first-hitting depth of its certified original trajectory. The canonical application
below uses full prefixes, so these lengths coincide there.

#### Strongest finite certificate retained by the theorem

For the explicitly defined finite family, (R.jointscore) retains the full residue
coupling and exact root denominators. It dominates the sum of individual block minima,
which in turn dominates the exact coefficient sum (R.blockcomparison) and the
selected-count multiplier (C.master). The resulting certificate hierarchy is
\[
 \text{shared residue allocation}
 \ \ge\ \text{separate block allocations}
 \ >\ \text{exact affine-coefficient comparison}
 \ \ge\ \text{certified cell/layer comparisons}.
\]
The rectangular \(E_b\) certificate is retained as a benchmark. In the canonical
completed family its rectangular blocks are contained in the full completed layers:
their original prefixes have zero height correction, their budgets are unchanged, and the
completion theorem recovers their vectors. The larger family is not obtained by changing
the definition of \(E_b\).

### C.7. Canonical certificates and density bounds

Here \(q=q_N\), \(p=P\), and
\(W_{\mathcal F}^{\rm joint}=W_{\mathcal F}^{\rm joint}(q_N,P)\).
The three certificates used here have the following exact data:

| Seed \(y\) | \(d\) | \(e\) | Full odd depth \(D\) | Ordinary time | Maximum odd state | \(\alpha_0\) |
|---:|---:|---:|---:|---:|---:|---|
| 101 | 4 | 1 | 7 | 25 | 101 | \(101/128\) |
| 193 | 5 | 2 | 43 | 119 | 3077 | \(193/256\) |
| 12289 | 8 | 2 | 14 | 50 | 12289 | \(12289/16384\) |

Their complete valuation words, in forward order and ending at the first hit of one, are:

```text
101:
  4, 1, 3, 1, 2, 3, 4

193:
  2, 2, 3, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2,
  1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1,
  3, 1, 1, 1, 4, 2, 2, 4, 3, 1, 1, 5, 4

12289:
  2, 2, 2, 2, 2, 4, 1, 5, 3, 3, 1, 2, 3, 4
```

Apply \(3y+1\), check the displayed exact valuation, and divide by its power of two at
every step. This reconstructs each finite certificate; no assumption about an
uncertified trajectory is needed.

The full-prefix leading data are

| Seed | \(A_D\) | \(\beta_D\) | \(\Gamma_D\) | \(\chi_D\) | Final \(T_D\) at \(b=2^{25}\) |
|---:|---:|---|---|---:|---:|
| 101 | 18 | \(2048/2187\) | \(2048/2187\) | 0 | 67,108,860 |
| 193 | 76 | \(2^{68}/3^{43}\) | \(262144/19683\) | 2 | 67,108,858 |
| 12289 | 36 | \(4194304/4782969\) | \(4194304/4782969\) | 0 | 67,108,857 |

All full-prefix \(\beta_D\) are less than one, and hence so are the earlier \(\beta_r\).
For 193, \(\Gamma_{43}\) lies strictly between four and sixteen, so the least height
correction is exactly two. Its earlier layers retain the smaller correction appropriate to each
prefix.

The base minimum-root excesses over \(16^b\) are, respectively,
\[
 \frac{5\,16^b-32}{96},\qquad
 \frac{16^b-64}{192},\qquad
 \frac{16^b-4096}{12288}.
\]
They are positive for \(b\ge4\), and the maximum certified odd state of each target is
below \(16^4\). These verify the finite base conditions. The analytic application continues
to use \(b=2^{25}\).

#### Exact score multiplier

For every seed and prefix, compute \(\beta_{y,r},\Gamma_{y,r},\chi_{y,r}\) from
(C.leading) and (C.heightdebit), and \(\Lambda_{y,r}\) from (C.selectedcount). Define
\[
 \boxed{
 \mathfrak A_b
 =1+\sum_{(y,d,D)=(101,4,7),(193,5,43),(12289,8,14)}
 \left[
 \frac1{\alpha_y}
 +\sum_{r=1}^D
 \frac{\Lambda_{y,r}(2b-d+e(y)-1-\chi_{y,r})}{\beta_{y,r}}
 \right].
 }
 \tag{C.factor}
\]
This is an exact rational definition involving 64 prefix layers. Each integer count is
evaluated by the finite-difference formula (C.quotienteval). It does not require a root
list, a residue table at the canonical \(q_N\), or an optimized value of \(c_{\rm FM}\).

At \(b=2^{25}\),
\[
 \begin{aligned}
 \mathfrak A_b
   &\approx2.9273409933096237\times10^{275},\\
 \mathfrak A_b^3
   &\approx2.5085337209674080\times10^{826},\\
 (\mathfrak A_b/E_b)^3
   &\approx2.0173520932097131\times10^{697}.
 \end{aligned}
\]
The following strict inequalities
\[
 \mathfrak A_b^3>\frac{250}{100}10^{826},\qquad
 (\mathfrak A_b/E_b)^3>\frac{201}{100}10^{697}
 \tag{C.numericguards}
\]
are checked by integer cross-multiplication of exact fractions. Decimal displays play no
role in the inequalities.

#### Benchmark root families

| Certificate | Fixed meaning | Guaranteed score multiplier over \(W_*\) |
|---|---|---:|
| \(C_b\) | One-coordinate period-nine lifts | \(57101167060327/1953295\approx2.9233253\times10^7\) |
| \(D_b\) | Rectangular multivariate volume estimate, prefixes \((7,13,13)\) | \(5.324667695451\ldots\times10^{42}\) |
| \(E_b\) | Exact rectangular counts with retained layers, prefixes \((7,15,14)\) | \(1.0753406914595744\ldots\times10^{43}\) |
| \(\mathfrak A_b\) | Residue-completed increments, height corrections, full prefixes \((7,43,14)\) | \(2.9273409933096237\ldots\times10^{275}\) |

For clarity, the one-coordinate and rectangular-volume benchmarks
are the literal quantities
\[
 \begin{aligned}
 C_b={}&1+\left(1+\left\lfloor\frac{2b-4}{9}\right\rfloor\right)
          \left(\frac{24}{19}+\frac{192}{145}\right)
       +\left(1+\left\lfloor\frac{2b-7}{9}\right\rfloor\right)\frac{12288}{9217},\\
 D_b={}&1+\frac{(2b-4)^7}{7!\,2^{11}3^{28}}
 +\frac{(2b-4)^{13}}{13!\,1269760\,3^{91}}
 +\frac{(2b-7)^{13}}{13!\,1310720\,3^{91}}.
 \end{aligned}
 \tag{C.earlier}
\]
The affine comparison and the rectangular simplex bound give these weaker
benchmarks by retaining their indicated blocks and leading ceilings.
The definition of \(E_b\) in (C.E) retains each earlier layer's sharper
coefficient. The full completed family contains those rectangular blocks:
their original prefixes have zero height correction and unchanged budgets.
None of these symbols is redefined to mean the larger completed family.
The exact counts and rational evaluations accompany the computational
evidence.

#### Domain and root clocks

The canonical block-count upper bound is
\[
 J_{\rm up}=1+
 2^6Q_7(\lfloor67108860/3\rfloor)+
 2^{42}Q_{43}(\lfloor67108860/3\rfloor)+
 2^{13}Q_{14}(\lfloor67108857/3\rfloor).
\]
The exact scalar check is
\[
 4J_{\rm up}<3\cdot2^{916}.
 \tag{C.countguard}
\]
Equations (C.master)–(C.domain) therefore give
\[
 0<\mathfrak A_bW_*<W_{\mathcal F}^{\rm joint}
 <2^{916-4b}=2^{-134216812}<2^{-4096}.
 \tag{C.domainguard}
\]
The feasible constant vector supplies this upper bound for the allocation
minimum.

The large relative factor has a separate absolute scale. All retained
mass bounds are at most \(W/\mu\), including (D.refinedmass), so
\[
 c_{\rm comp}(W)\le\frac{32}{225}(e^{9W/4}-1)\le\frac{16}{25}W<W
 \qquad(0<W\le2^{-4096}),
\]
using \(e^z-1\le z/(1-z)\le2z\) for \(0\le z\le1/2\). Thus the strengthened **certified formula
itself** remains smaller than \(2^{-134216812}\). The displayed power is a small-score
domain condition, not an evaluation of
the absolute density formula. The further level loss is quantified
for the named formulas in (Q.formulascale) and (Q.refinedscale).
Neither statement bounds the actual convergence
density from above.

The ordinary root-clock excess over the indexed baseline root \(R_s\), whose clock is \(2s+1\), is
\[
 e(y)+\tau_1(y)-2d=
 \begin{cases}18,&y=101,\\111,&y=193,\\36,&y=12289.\end{cases}
\]
The baseline block is retained, and every seed's zero block is retained. Thus the largest
root is exactly the largest baseline root, and the largest root clock is exactly the old
maximum plus 111. None of the quotient vectors, residue choices, prefix lengths, or
height corrections changes these formulas.

#### Consequence for the density formula

Apply (D.finitepool) to the completed family with target one, and apply
(Q.cubicscore) directly to the pairs
\((W_*,\mathfrak A_bW_*)\), \((E_bW_*,\mathfrak A_bW_*)\), and
\((\mathfrak A_bW_*,W_{\mathcal F}^{\rm joint})\).
Their hypotheses follow from (C.domainguard), (C.numericguards),
and positivity of \(E_b\).
With the constants named in (I.constants), this proves (I.rootdensity).
For every \(c>c_0\),
\[
 \begin{aligned}
 \underline d(\mathcal G_c)
 &\ge c_{\rm FM}(W_{\mathcal F}^{\rm joint})
 >c_{\rm FM}(\mathfrak A_bW_*)
 >2.50\times10^{826}\,c_{\rm FM}(W_*),\\
 c_{\rm FM}(\mathfrak A_bW_*)
 &>2.01\times10^{697}\,c_{\rm FM}(E_bW_*).
 \end{aligned}
 \tag{C.densitygain}
\]
These compare certified lower-bound formulas at the same analytic
envelope and moment tables. They do not compare actual densities or
evaluate the absolute optimized constant. The second line follows
from the literal score pair, not division of independent lower bounds.
The primary quantitative improvement of this appendix is the score
guarantee (C.master).

Within these three fixed prefixes and incoming budgets, replacing every
selected count and every reciprocal coefficient by its allowed upper
bound changes the additive comparison factor by at most
\[
 \frac{1+(4/3)(J_{\rm up}-1)}{\mathfrak A_b}
 =1.1989376587603659\ldots<1.199.
 \tag{C.localceiling}
\]
Every block coefficient exceeds \(3/4\), so each contributes less than
\(4/3\), and (C.blockcount) bounds the number. This bounds that additive
coefficient comparison only. It does not bound the shared allocation
minimum, other seeds, or a changed height geometry.

The combined refined bound is
\(\underline d(\mathcal G_c)\ge c_{\rm comp}(W_{\mathcal F}^{\rm joint})\)
for every \(c>c_0\), by (D.finitepool). Equation (Q.sixteengain) makes
it strictly larger than the pure-fractional bound displayed here.
The cubic multipliers in (C.densitygain) retain their named
\(c_{\rm FM}\) meaning; (Q.sixteencubic) supplies the corresponding
comparison for \(c_{{\rm FM},16}\), not for \(c_{\rm comp}\).

### C.8. A shared-allocation example: the 101 block

There is a strict gain beyond summing separate minima even before the
valuation extension. For the base block
\[
 M_s=\frac{101}{128}R_s-\frac9{128},
 \qquad
 \phi(r)=128^{-1}(101r-9)\pmod{3^q},
\]
the affine permutation sends the baseline root residue to the new one.
Writing \(\alpha=101/128\), the valuation identity gives
\[
 \phi^k(r)-r=(\alpha^k-1)(r+1/3),\qquad
 \nu_3(\phi^k(r)-r)=2+\nu_3(k)
 \quad(k\ge1).
 \tag{C.101orbits}
\]
Indeed \(\nu_3(\alpha-1)=3\); cubing a unit congruent to one modulo
three raises the valuation of its difference from one by one, and an
exponent prime to three preserves it. Also
\(\nu_3(r+1/3)=-1\) for every integer \(r\). Thus, for \(q\ge3\),
every unit orbit has length \(3^{q-2}\).

For \(q\ge4\), \(0<p\le1\), both separate allocation minima uniquely
fill the largest roots first, to the common cap
\(B_q=(2/3)2^q\), with at most one partial entry. This follows by
transferring mass from a larger reciprocal cost to a smaller one; all
costs are distinct. Their minimizing index vectors therefore agree.
A common residue-labeled minimizer would have to be \(\phi\)-invariant.
Its nonempty support has size
\[
 \left\lceil\frac{K_qp}{B_q}\right\rceil
 \le \left\lceil(3/2)^q\right\rceil<3^{q-2}.
\]
For the last inequality,
\((3/2)^q/3^{q-2}=9/2^q\le9/16\) and \(3^{q-2}\ge9\).
Such a support cannot contain a whole orbit. By (R.jointdominance),
\[
 W_{\{R,M\}}^{\rm joint}(q,p)>W(q,p)+W_{101}(q,p)
 >(1+128/101)W(q,p).
 \tag{C.strict101}
\]
No invariance of \(g_N\) under \(\phi\) is used. The strict conclusion
excludes \(p=0\); at \(q=1,2\) the affine map is the identity. This
argument supplies strictness without a numerical lower bound on the
extra shared-allocation gap.

### C.9. Limits at fixed height

The completed construction remains in a specific height geometry.
Put \(X=16^b\), with the canonical \(b=2^{25}\). Its affine blocks have
\[
 M_s=4^{s-H}n+\frac{4^{s-H}-1}{3},\qquad
 X\le n\le R_H=\frac{4X-1}{3}.
\]
To preserve exactly the baseline unit index set, one requires
\(n\equiv2\pmod3\), since \(H\equiv2\pmod3\).
For an odd \(n\) in this interval, the next odd value is below \(X\)
exactly when \(\nu_2(3n+1)\ge2\): valuation one gives a value exceeding
\(X\), while valuation at least two gives a value at most \(X\),
with equality impossible for an odd output. Hence \(n\equiv1\pmod4\).
As \(X\equiv4\pmod{36}\), the exact list satisfying these structural
conditions is
\[
 n=X+1+12j,\quad 0\le j\le\frac{X-4}{36},
 \qquad J_{\rm struct}=\frac{X+32}{36}.
 \tag{C.structuralcount}
\]
This counts candidates. Convergence and the remaining trajectory-height
conditions still require certificates. Distinct seed descriptions cannot
be counted twice if they give the same \(n\).

There is a separate upper bound on the score obtainable within this
geometry. For \(J\ge1\) distinct such complete blocks, put
\(K=K_q=2\cdot3^{q-1}\) and \(\ell=\lfloor K/(2J)\rfloor\).
Remove the \(\ell\) smallest-index roots from every block and exclude
all their residue classes. At least \(K/2\) residues remain, and every
root at a remaining residue is at least \(X4^\ell\). Assign total mass
\(KP\) uniformly to the remaining residues. Its entries are at most
\(2P\le2\le B_q\), so it is feasible for (R.jointscore). Therefore
\[
 W_{\mathcal F}^{\rm joint}
 \le \frac{KPJ}{X}\,4^{-\ell}.
 \tag{C.geometryceiling}
\]
At the canonical level, \(N\ge17\): \(V_N\le1\) cannot hold
at \(N=16\), since \(t\ge4b\), \(\lambda>1/4\), and
\(V_{16}>2^{4b-32}>1\). Consequently \(q\ge17b\ge16b\),
\(K\ge2^q\ge X^4\), and \(J\le J_{\rm struct}\le X\).
It follows that
\[
 \ell\ge K/(4X)\ge2^{12b-2},\qquad
 K\le\ell^2\le2^\ell,\qquad
 W_{\mathcal F}^{\rm joint}
 \le2^{-\ell}\le2^{-\,2^{402653182}}.
 \tag{C.fixedceiling}
\]
The floor costs at most a factor two, and
\(\ell\ge\sqrt K\), since \(K\ge X^4\ge16X^2\).
The integer inequality \(\ell^2\le2^\ell\) holds for \(\ell\ge4\).
This bounds the stated mean-and-capacity allocation certificate.
Since \(c_{\rm comp}(W)<W\) in the small-score domain, it also bounds
that formula. It places no upper bound on the actual density of
convergent integers. Other height geometries or stronger information
about the reference marks are outside this counting ceiling.


## Appendix D. Further consequences of the reference-law estimates {#appendix_reference_consequences}

This appendix records consequences of the reference-law estimates beyond
the three branches used in the explicit density recipe (D.densityrecipe).
Convex-order inequalities propagate the whole concentration profile,
whose finite allocation problem gives (D.profiledensity). Projectivity
and summable mixing also give bounded relative entropy (F.entropybound).
These results require no change to the root or counting constructions;
a strict numerical improvement from the profile remains unproved.

The notation is inherited from Sections 9 and 10:
\(f_n\) has mean one on \(G_n\), \(H_m\) has mean \(\mu=8/9\),
and \(L=2\log2\) is the limiting capacity coefficient. In Section D.2,
\(W\) is a source-family score in the range of (D.mass), and
\(p_m=(W-\kappa\epsilon_m)_+\) is its coarse marked-mass bound.
The symbols \(D_s(n)\) and \(r_s\) in Section D.3 denote divergence
and its rate; they are unrelated to the seed-prefix depth \(D\)
in Appendix C.

### D.1. Convex-order inequalities for the reference density and fan {#appendix_convex}

The affine mixture (F.mixture), which proves the moment inequality
(F.inheritance), also permits a general convex test.

**Proposition (convex-order inequality).** For every finite convex function
\(\Phi:[0,\infty)\to\mathbb R\) and integers \(u,v\ge0\),
\[
 \langle\Phi(f_{u+v})\rangle_{u+v}
 \le\frac1{3^{u+v}}\sum_{x\in G_u}\sum_{y\in G_v}
                 \Phi(f_u(x)f_v(y)).                 \tag{F.convex}
\]

*Proof.* Fix \(y\) in (F.mixture). If \(f_v(y)>0\), divide its
coefficients by their sum \(f_v(y)\) and apply Jensen to the convex
function \(z\mapsto\Phi(f_v(y)z)\). Averaging over the affine
permutations of \(G_u\) gives
\[
 3^{-u}\sum_{z\in G_u}\Phi(f_{u+v}(y+3^vz))
 \le3^{-u}\sum_{x\in G_u}\Phi(f_v(y)f_u(x)).
\]
If \(f_v(y)=0\), both sides equal \(\Phi(0)\). Average over \(y\).
The countable mixture can be grouped by the finitely many values of
\(f_u\), so ordinary finite Jensen suffices. A zero-length block gives
equality. \(\square\)

Both compared distributions have mean one. Thus (F.convex) is a
convex-order bound: every convex test has no larger average for the
combined law than for the product of the two independent finite-table
variables. Moment inheritance is its power-function specialization.
The positive-part tests used in (D.hinge) will retain more of the upper
tail than one power moment.

The same mixture gives the version needed for the whole fan:
\[
 \langle\Phi(H_{u+v})\rangle_{u+v}
 \le\frac1{3^{u+v}}\sum_{x\in G_u}\sum_{y\in G_v}
                   \Phi(f_u(x)H_v(y)).               \tag{F.convexfan}
\]
To prove this, split \(f_{u+v+1}\) into a prefix of length \(u\)
and a suffix of length \(v+1\). In the fiberwise proof of (F.convex),
restrict the suffix residue to the \(2\bmod3\) coset and replace the
test by \(z\mapsto\Phi(4z/9)\). The bijections \(\phi_{u+v}\)
and \(\phi_v\) turn the two sides into (F.convexfan). The suffix
coset has \(3^v\) elements, giving the displayed normalization.
This also covers \(v=0\), for which the suffix has length one and
\(H_0=8/9\). Both sides have mean \(8/9\).
Repeated application therefore bounds convex tests by product
distributions; it need not recover the exact distribution of \(H_{u+v}\).

### D.2. The full concentration profile and optimal residue allocation {#appendix_profiles}

The moment-to-mass estimate (D.generalp) is one way to use residue capacity. The following
finite optimization records the strongest bound obtained from the
whole marker distribution and that capacity alone.

**Proposition (optimal capacity bound).** Fix \(m\ge2\), put \(Q=3^m\),
and let \(0\le p\le L\mu\). Define
\[
 \mathcal C_m(p)=
 \min\left\{\sum_{r\in G_m}w_r:
      0\le w_r\le L/Q,\quad
      \sum_{r\in G_m}w_rH_m(r)\ge p\right\}.
                                                        \tag{D.allocation}
\]
Then
\[
 \mathcal C_m(p)=
 \sup_{t>0}
 \frac{\bigl[p-L\langle(H_m-t)_+\rangle_m\bigr]_+}{t},
 \qquad 0\le\mathcal C_m(p)\le p/\mu.                 \tag{D.hinge}
\]

*Proof.* Put \(h_r=H_m(r)\) and \(c=L/Q\). For every admissible
allocation and \(t>0\),
\[
 p\le\sum_rw_rh_r
 \le t\sum_rw_r+c\sum_r(h_r-t)_+.
\]
This proves the lower bound by the displayed supremum. To attain it
when \(p>0\), order the entries as \(h_1\ge\cdots\ge h_Q\)
and let \(j\) be the least index with \(c\sum_{i\le j}h_i\ge p\).
Feasibility follows from \(c\sum_i h_i=L\mu\), and \(h_j>0\).
Fill the first \(j-1\) entries to capacity, allocate
\((p-c\sum_{i<j}h_i)/h_j\) at entry \(j\), and leave the others
empty. The mass is
\[
 c(j-1)+\frac{p-c\sum_{i<j}h_i}{h_j}.
\]
Choosing \(t=h_j\) in (D.hinge) gives exactly this number, including
ties. Thus there is an optimizer with at most one partially occupied
entry. At \(p=0\), both sides are zero. The uniform allocation
\(w_r=p/(Q\mu)\) is feasible and has mass \(p/\mu\), proving
the upper bound. \(\square\)

For any finite set \(\mathcal S\subset(1,\infty)\) of orders with
valid moment ceilings, the allocation optimum dominates all their
capacity lower bounds simultaneously:
\[
 \max\bigl(\{u_m^{\rm comp}(W)\}\cup
            \{v_{s,m}(W):s\in\mathcal S\}\bigr)
 \le\mathcal C_m(p_m)\le W/\mu.                     \tag{D.profiledominates}
\]
The zero-residual case is immediate. Otherwise apply (D.capacity),
(D.generalp), and (D.complementexplicit) to an allocation attaining
\(\mathcal C_m(p_m)\). Its mass is at most
\(p_m/\mu\le W/\mu<L/2\), so the centered inverse uses exactly
the increasing branch justified in (D.inverse). Hölder gives each other
branch. There is no implied ordering of the bounds as \(s\) decreases.
For example, for a constant marker one, capacity coefficient one and
residual mass \(1/2\), the order \(2,3/2,5/4\) bounds are
respectively \(1/4,1/8,1/32\).

The feasible range is exact. At \(p=L\mu\), all positive-marker
entries may be filled and zero-marker entries left empty. If \(p>L\mu\),
no allocation is feasible, and the hinge supremum is infinite as
\(t\downarrow0\). Optimality here concerns the residue-capacity
constraints, not realization of an optimizing allocation by integer orbits.

For actual finite source families the coefficient is
\(T_X=T_{X,3^m,R_X}\), not \(L\). If \(p_X\ge0\) is a
guaranteed coarse marked mass at that cutoff, the correct finite inequality is
\[
 U_X\ge
 \frac{\bigl[p_X-T_X\langle(H_m-t)_+\rangle_m\bigr]_+}{t}.
                                                        \tag{D.finitehinge}
\]
For fixed \(m\), any strict lower bound below \(\mathcal C_m(p_m)\)
can be witnessed by one fixed threshold \(t>0\). First choose that
threshold, then a sufficiently small fixed graft tolerance, then a
cutoff beyond which \(T_X\) and the coarse error bound have their required
accuracy. This proves the analogue of (D.mass) with
\(\mathcal C_m(p_m)\) in place of \(u_m(W)\). Its radial domain follows
from \(\mathcal C_m(p_m)\le W/\mu\). Consequently (D.radial) also
gives the valid fixed-level bound
\[
 \underline d(\mathcal G_c)\ge\mathcal D(\mathcal C_m(p_m)).
                                                        \tag{D.profiledensity}
\]
Only a fixed threshold is needed before the cutoff limit.

The functions \(z\mapsto(z-t)_+\) are increasing and convex.
Thus (F.convexfan), and finite pointwise upper tables with directed
rounding, can supply upper bounds for their averages. General convex
tests need not be increasing and cannot automatically use such upper
tables. An efficient representation of these propagated profiles would permit
quantitative comparison with the explicit bound \(c_{\rm comp}\) and the
exact two-sided inverse in (D.twosidedcapacity).

### D.3. Rényi divergence rates and bounded relative entropy {#appendix_entropy}

For \(s>1\) define the Rényi divergence from the uniform law, with
relative entropy at order one, by
\[
 D_s(n)=\frac{\log M_s(n)}{s-1},\qquad
 D_1(n)=\langle f_n\log f_n\rangle_n,
 \quad 0\log0:=0.
\]
These are normalized using the mean-one density \(f_n\).

**Proposition (rates justified by inheritance).** For every \(s\ge1\),
\[
 r_s:=\lim_{n\to\infty}\frac{D_s(n)}n
     =\inf_{n\ge1}\frac{D_s(n)}n\ge0.               \tag{F.divergencerate}
\]
The rates are nondecreasing in \(s\), and
\(\lim_{s\downarrow1}r_s=r_1\). For a fixed \(s>1\), if a block length
\(\ell\ge1\) has certificates \(M_s(j)\le B_j\) for
\(0\le j\le\ell\), with \(B_0=1\), then
\[
 D_s(n)\le n\bar r_s+O_{s,\ell}(1),\qquad
 \bar r_s=\frac{\log B_\ell}{(s-1)\ell}\ge r_s.
                                                        \tag{F.blockrate}
\]
The implicit constant here also depends on the fixed finite certificates.

*Proof.* For \(s>1\), (F.inheritance) makes \(D_s\) subadditive;
Jensen gives nonnegativity. Finite-level differentiation at order one
gives \(D_s(n)\to D_1(n)\), including zero entries by continuity.
Taking this limit in subadditivity proves it also for \(D_1\).
For any nonnegative subadditive sequence \(a_n\), write
\(n=k\ell+j\), \(0\le j<\ell\). Then
\(a_n\le ka_\ell+a_j\), so
\(\limsup a_n/n\le a_\ell/\ell\). Taking the infimum over
\(\ell\) and using the opposite bound from the definition of the
infimum proves (F.divergencerate). The same division into blocks using
\(\log B_j/(s-1)\) proves (F.blockrate).

For a finite mean-one density, Hölder makes
\(s\mapsto\log\langle f^s\rangle\) convex. Its value at one
is zero, so its secant slope from one, \(D_s\), is nondecreasing.
Thus \(r_s\) is nondecreasing, and the two infima commute:
\[
 \inf_{s>1}r_s
 =\inf_{s>1}\inf_{n\ge1}\frac{D_s(n)}n
 =\inf_{n\ge1}\inf_{s>1}\frac{D_s(n)}n=r_1.
\]
This proves the order-one limit. \(\square\)

For a fixed \(s>1\), subadditivity gives \(D_s(n)=nr_s+o(n)\);
by itself it does not upgrade that remainder to \(O(1)\) at the true
rate. The block rate \(\bar r_s\) is a certified upper bound. At
order one, projectivity and the summable mixing envelope give more.

**Proposition (bounded order-one divergence).** For every \(n\ge2\),
\[
 0\le D_1(n)-D_1(n-1)\le\min\{\log3,\epsilon_{n-1}\}.             \tag{F.entropyincrement}
\]
Consequently \(D_1(n)\) increases to a finite limit \(D_1^\infty\), and
\[
 \begin{split}
 \sup_{n\ge0}D_1(n)=D_1^\infty
 &\le\frac23\log2+
       \sum_{j\ge1}\min\{\log3,C_6j^{-2314/25}\}<\infty,\\
 0\le D_1^\infty-D_1(n)&\le\sum_{j\ge n}\min\{\log3,\epsilon_j\}
       \qquad(n\ge1),\\
 r_1&=0,\qquad\lim_{s\downarrow1}r_s=0.
 \end{split}                                        \tag{F.entropybound}
\]

*Proof.* Fix \(n\ge2\) and put \(g=f_{n-1}\circ\pi_{n,n-1}\).
By the projectivity following (T.law), \(g\) is the average of
\(f_n\) on each three-point fiber. Nonnegativity gives \(f_n=0\)
on a zero-\(g\) fiber, and \(0\le f_n/g\le3\) on every other fiber.

For \(0\le u\le3\), define \(\phi(u)=u\log u-u+1\), with
\(0\log0=0\). Convexity and its minimum at one give
\(\phi(u)\ge0\). If \(u\le1\), then \(u\log u\le0\), so
\(\phi(u)\le1-u\). If \(1\le u\le3\), its chord from one to three gives
\[
 \phi(u)\le\frac{3\log3-2}{2}(u-1)\le u-1.
\]
Here \(\log3=(\log_2 3)\log2<(8/5)(7/10)=28/25<4/3\),
using the elementary logarithmic inequalities already established in the
construction. Thus \(0\le\phi(u)\le|u-1|\) on the whole interval.

On each nonzero fiber, the sum of \(f_n-g\) is zero and \(\log g\)
is constant. These facts cancel the linear and \(\log g\) terms in
the entropy difference, giving
\[
 D_1(n)-D_1(n-1)
 =\langle g\phi(f_n/g)\rangle_n
 \le\langle|f_n-g|\rangle_n\le\epsilon_{n-1}.
\]
The integrand is defined as zero on zero-\(g\) fibers. Its
nonnegativity proves the lower bound; the last inequality is precisely
the unhalved bound (T.mix). The same fiber cancellation also writes the
increment as \(\langle f_n\log(f_n/g)\rangle_n\).
Since \(f_n/g\le3\) wherever \(f_n>0\) and \(\langle f_n\rangle_n=1\),
this is at most \(\log3\), proving (F.entropyincrement).

At level zero \(f_0=1\), while the even and odd geometric letters
give \(f_1(0)=0,f_1(1)=1,f_1(2)=2\). Hence
\(D_1(0)=0\) and \(D_1(1)=(2/3)\log2\).
Summing (F.entropyincrement) and using (M.envelope) proves boundedness,
since \(2314/25>1\). Summing from \(n+1\) onward gives the stated
tail. Boundedness gives \(r_1=0\), and (F.divergencerate) gives the
right-hand limit in the order \(s\). \(\square\)

For scale, the following values are certified to round to four decimal
places; the complete record covers every \(0\le n\le16\).

| \(n\) | 1 | 2 | 4 | 8 | 12 | 16 |
|---|---:|---:|---:|---:|---:|---:|
| \(D_1(n)\) | 0.4621 | 0.6304 | 0.8240 | 1.0087 | 1.1008 | 1.1544 |
| \(D_1(n)/n\) | 0.4621 | 0.3152 | 0.2060 | 0.1261 | 0.0917 | 0.0721 |

These are finite-level values, not an estimate of \(D_1^\infty\).
The comparison \(\bar r_{3/2}=(\log b_{12})/6\approx0.1247\)
is a certified block-rate upper bound from (F.blockrate), not an
identified value of \(r_{3/2}\). The proof identifies \(r_1=0\).

The computation uses positive upper arrays as in
[Section 9](#chapter09),
rather than treating their rounded entries as the exact law.
For an upper density \(h\ge f_n\), put
\(\eta=\langle h\rangle_n-1\), \(B=\max h\), and
\(T=\langle h\log h\rangle_n\). For \(0<\eta<1\),
\[
 T-\eta(\log B+1)\le D_1(n)\le T-\eta\log\eta.
                                                        \tag{F.entropyrounding}
\]
Indeed, with \(d=h-f_n\ge0\), the identity
\(h\log h-f_n\log f_n=d\log h+f_n\log(h/f_n)\)
and \(\log(1+x)\le x\) bound this difference above by
\(d(\log B+1)\) and below by \(d\log d\).
Zero entries are interpreted by continuity. Averaging and convexity of
\(d\log d\) prove the two bounds; at \(\eta=0\), \(h=f_n\).
Rational logarithm enclosures and this correction give intervals of
width less than \(1.3\times10^{-7}\) for the displayed entropies.
The archive contains the rational interval endpoints determining the
displayed rounding.

The tail estimate concerns convergence as the level \(n\) increases.
It gives no quantitative rate as \(s\downarrow1\), no conclusion
\(r_s=0\) at a fixed \(s>1\), and no polynomial moment bound at
orders \(3/2\) or \(2\). Nor does it improve the optimized density
constant without a further quantitative capacity comparison. For the fan, whose
mean is \(\mu=8/9\), divergence is computed from \(H_m/\mu\).
The capacity branches retain their residual-mass powers and
capacity coefficient.

## Appendix E. Primitive decay from the original pair process {#appendix_primitive_local}

We prove an explicit primitive Fourier-decay estimate for the reference law.
The argument uses the pairing and separated-triangle method of Tao
[1, Section 7] and its quantitative development in [3]. Working directly with
the original pair process gives an exact binomial first-passage law. Its
exponential moment yields a linear vertical window and the degree-four
recurrence used to specify the coefficient.

### E.1. Primitive Fourier decay and its coefficient

Let independent positive integers \(K_i\) satisfy
\(\Pr(K_i=a)=2^{-a}\), and put
\[
 X_n=\sum_{i=1}^n3^{i-1}2^{-(K_1+\cdots+K_i)}\pmod{3^n},
 \qquad F_n(\xi)=\mathbb E e^{2\pi i\xi X_n/3^n}.
                                                               \tag{E.law}
\]
This is (T.law), with the unnormalized positive Fourier convention of
Section 6. All inverse powers of two are taken in the indicated residue ring.

For a positive integer \(B\), define
\[
 \epsilon=2^{-78},\quad d=\epsilon^2/2,\quad
 \eta=d/(32B),\quad \delta=(16\cdot10^B)^{-1},
\]
\[
 K=16(B+1)/\epsilon^2,\quad R=4(K+16(B+1))+1,
 \quad A=64/\delta,\quad H=2^{17}A^2/\delta.
\]
The symbols \(K,R,A,H\) in this appendix are local parameters; in particular
\(K\) is not a valuation letter \(K_i\). They are positive integers. Set
\[
 u(p)=H(p+1)^4,\qquad v_0=K,\qquad
 v_{i+1}=v_i+u(v_i)+K+2\quad(0\le i<R),
\]
\[
 P=v_R+K+2,\qquad Z=128A(P+1)^2/\delta,
\]
\[
 M=\left\lceil\max\left\{
 64B/d,\ 20(P+1),\ (2560(B+1))^2,\ Z^2/\eta,\ 4096
 \right\}\right\rceil,\qquad C_B^{\rm loc}=(3M)^B.   \tag{E.recipe}
\]
This is a finite integer recipe fixed before the level and frequency.

**Theorem (local primitive decay).** For every positive integer \(B\),
every \(n\ge1\), and every \(\xi\) with \(3\nmid\xi\),
\[
 |F_n(\xi)|\le C_B^{\rm loc}n^{-B}.                 \tag{E.primitive}
\]
For real requested order \(b>0\), the integer order \(B=\lceil b\rceil\)
supplies the same assertion with \(n^{-b}\). We prove the theorem below.

### E.2. Pairing and the discounted process

Fix \(n,\xi\) as in the theorem and let \(N=\lfloor n/2\rfloor\).
The case \(n=1\) follows from \(|F_n|\le1\); assume \(n\ge2\).
Put \(B_j=K_{2j-1}+K_{2j}\) and \(S_j=B_1+\cdots+B_j\), with \(S_0=0\).
Then
\[
 \Pr(B_j=b)=(b-1)2^{-b}\quad(b\ge2).
\]
Conditional on a pair sum \(b\), its first letter is uniform on
\(1,\ldots,b-1\). The contribution of that pair, after \(j\) preceding
pairs and total valuation \(l\), is
\[
 3^{2j}2^{-l}\bigl(2^{-a}+3\,2^{-b}\bigr).
\]
The conditional character is a unit-modulus factor times
\((b-1)^{-1}\sum_{a=1}^{b-1}e_{3^n}(\xi3^{2j}2^{-(l+a)})\).
Its modulus is at most one. When \(b=3\), that modulus is
\(\cos(\pi\theta(j,l))\), where
\[
 \theta(j,l)=\operatorname{bal}\left(
 \frac{\xi3^{2j}2^{-(l+2)}}{3^n}\right)\in(-1/2,1/2]
 \quad(0\le j<N,\ l\in\mathbb Z).                 \tag{E.phase}
\]
Here \(\operatorname{bal}\) selects the balanced representative modulo one.
Call a point black if \(|\theta|\le\epsilon\), and white otherwise.
Since \(1-\cos(\pi t)\ge2t^2\) for \(|t|\le1/2\), the pair factor at a
white state is at most \(1-2\epsilon^2\) when the next pair sum is three.

Given the pair sums, different first-letter choices are independent, and
the state of each pair depends only on earlier pair sums. Multiplying these
conditional bounds and bounding a possible last odd letter by one gives
\[
 |F_n(\xi)|\le U(0,0),
\]
where \(U(j,l)\) is the expectation, from that state, of the product up to
column \(N\) of
\[
 (1-2\epsilon^2)^{\mathbf1_W(j+t,l+S_t)
                             \mathbf1_{\{B_{t+1}=3\}}}.         \tag{E.kill}
\]
Set \(U=1\) at and beyond \(N\); in particular \(0\le U\le1\).
At a white state the one-step kernel has total mass
\(1-\tfrac14(2\epsilon^2)=1-d\). For products of the discount factors we use
\((1-2\epsilon^2)^k\le e^{-2\epsilon^2 k}\).

### E.3. Black triangles and separation

**Lemma (geometry).** The black lattice points are partitioned into triangles
\[
 \Delta=\{(j,l):j\ge j_0,\ l\le l_0,
       (j-j_0)\log9+(l_0-l)\log2\le t\},             \tag{E.triangle}
\]
with integer corners \((j_0,l_0)\), \(j_0\ge0\), and \(t\ge0\).
Every triangle lies in \(j\le N-16\). Every lattice point in the state
space \(0\le j<N\), outside a triangle but within distance sixteen of it,
is white. Here distance is Euclidean distance to the triangle's lattice
points. Distinct triangles have disjoint lattice points.

*Proof.* The exact phase relations are
\[
 \theta(j+1,l)=9\theta(j,l)\pmod1,\qquad
 \theta(j,l-1)=2\theta(j,l)\pmod1.                   \tag{E.phase-steps}
\]
Call a point weakly black if its phase has modulus at most \(1/100\).
Three elementary implications will be used. A weakly black point with a
black east or south neighbor is black, since multiplication by nine or two
does not wrap at that size. If east and south neighbors are weakly black,
the identity \(\theta=\theta_{\rm east}-4\theta_{\rm south}\pmod1\)
first bounds the parent by \(5/100\); its doubled phase then equals the
south phase as a real number and bounds it by \(1/200\). If west and south
neighbors are weakly black, the west relation first bounds the parent by
\(9/100\); doubling again bounds it by \(1/200\).

Starting from a black point \((j,l)\), move up along its black run to the
last black point \((j,l_0)\), then left along the black row to its first
black point \((j_0,l_0)\), possibly at \(j_0=0\). The upward run is finite:
otherwise its nonzero phase would halve indefinitely, contradicting its
minimum modulus \(3^{-(n-2j)}\). Write
\(|\theta(j_0,l_0)|=\epsilon e^{-t}\). Multiplication along the known black
row and column does not wrap, so the starting point belongs to (E.triangle).
The same multiplication formula makes every lattice point in that triangle
black.

For the collar put \(r=16\). All amplifications below are at most
\(18^{r+1}\), and \(100\cdot18^{17}<2^{78}\). Thus they carry a phase of
modulus at most \(\epsilon\) to one of modulus less than \(1/100\).
For a point southeast of the corner and within distance \(r\), its excess
logarithmic weight over the triangle is at most \(r(\log9+\log2)\).
Outside the triangle its phase is therefore strictly between \(\epsilon\)
and \(1/100\), with no wraparound; it is white.

For a northeast point \((j',l')\) with \(l_0<l'\le l_0+r\), suppose it
were black. Multiply down to height \(l_0+1\). Propagate weak blackness
left to column \(j\) using east and south neighbors if \(j'\ge j\),
or right using west and south neighbors if \(j'<j\). The necessary lower
row inside the triangle is black. Beyond its last top-row column it is
still weakly black: at most sixteen additional east steps give modulus
at most \(\epsilon9^{16}<2^{-27}<1/100\). The resulting weakly black
point \((j,l_0+1)\), with black south neighbor, is black, contradicting
the choice of \(l_0\).

For a point west of the corner, \(j_0-r\le j'<j_0\), suppose it were
black. Amplify east to column \(j_0-1\). If \(l'\ge l_0\), amplify down
to \(l_0\); if \(l'<l_0\), propagate weak blackness upward using east
and south neighbors. The east column is weakly black throughout the required
range because \((l_0-l')\log2\le t+r\log2\). The point
\((j_0-1,l_0)\) is weakly black and has a black east neighbor, so is black,
contradicting the choice of \(j_0\). There is no west case when \(j_0=0\).
These cases prove the collar.

Each lattice triangle is connected to its corner by north and west unit
steps. Two intersecting lattice triangles must have the same lattice set:
a path from an intersection to a point in their difference would cross the
white collar. They then have the same extreme corner and, by its phase,
the same \(t\). This gives the asserted partition.
Finally the corner phase is at least \(3^{-(n-2j_0)}\), whence
\[
 j_0+t/\log9\le n/2+\log\epsilon/\log9.
\]
Since \(9^{17}<2^{78}\), this places the whole triangle before
\(j=N-16\). \(\square\)

### E.4. First passage and white exits

For integer \(s\ge0\), let
\(J_s=\min\{j\ge1:S_j>s\}\) and \(H_s=S_{J_s}-s\).
Realize each geometric letter as the waiting time for one success of fair
coin tosses. If \(T_s\) counts the successes in the first \(s\) tosses,
then
\[
 T_s\sim\operatorname{Bin}(s,1/2),\qquad
 J_s=\lfloor T_s/2\rfloor+1.                        \tag{E.passage}
\]
Conditional on \(T_s\), the overshoot waits for two more successes when
\(T_s\) is even and one when it is odd. Future tosses are independent.
Consequently, for integers \(j,h\ge1\), with out-of-range binomial
coefficients zero,
\[
 \Pr(J_s=j,H_s=h)=2^{-s-h}
 \left[\binom{s}{2j-2}(h-1)+\binom{s}{2j-1}\right].  \tag{E.joint}
\]
In particular
\[
 J_s\le s/2+1,\quad \mathbb EH_s\le4,\quad
 \Pr(H_s>h)\le(h+1)2^{-h}.                          \tag{E.overshoot}
\]
For \(s\ge1,a>0\), the variance \(s/4\) of \(T_s\) gives
\[
 \Pr(|J_s-s/4|>a\sqrt{s}+1)\le(16a^2)^{-1},\qquad
 \sup_j\Pr(J_s=j)\le4/\sqrt{s}.                     \tag{E.passage-bounds}
\]
For the atom bound, each atom is the sum of two binomial atoms.
The central estimate \(\binom{2k}{k}/4^k\le1/\sqrt{k+1}\) follows by
induction: its squared step is
\((2k+1)^2(k+2)\le4(k+1)^3\), with difference \(3k+2\).
The odd case follows from the neighboring even case, so one binomial atom
is at most \(\sqrt{2/(s+1)}\), proving the displayed bound.

For \(s\ge1\) and \(t\ge0\), we also use
\[
 \Pr(T_s-s/2\ge t)\le e^{-2t^2/s}.                  \tag{E.binomial-tail}
\]
Indeed its centered exponential moment is \(\cosh(a/2)^s\le e^{sa^2/8}\),
by integrating \(\tanh x\le x\); exponential Markov with \(a=4t/s\)
gives the claim.

Start at \((j,l)\) in a triangle with top \(l_0\), and set \(s=l_0-l\).
Except with probability \(e^{-8}\),
\(J_s\le s/4+\sqrt{s}+1\); for \(s=0\) this holds deterministically.
The top right corner is at least \(s\log2/\log9\) columns to the right
of \(j\). Since \(\log2/\log9>5/16\) and
\(\sqrt{s}\le s/16+4\), the exit's horizontal overshoot past the last
top-row lattice point is less than six. Also \(H_s\le8\) except with
probability \(9/256\). On their intersection the exit lies outside the
triangle within distance ten, and is before \(N\). Its collar makes it
white. Thus
\[
 \Pr\bigl((j+J_s,l_0+H_s)\text{ is white}\bigr)
 \ge1-e^{-8}-9/256>15/16.                           \tag{E.white-exit}
\]

### E.5. Long crossings and the degree-four threshold

Observe the process \(p\ge0\) steps after that exit. Its position is
\((j+J_s+p,l_0+V_p)\), where
\(V_p=H_s+B_{J_s+1}+\cdots+B_{J_s+p}\).
For \(1<z<2\), a geometric letter has moment \(z/(2-z)\).
Conditional on the parity at time \(s\), \(V_p\) is the sum of either
\(2p+1\) or \(2p+2\) fresh geometric letters. Hence
\(\mathbb E(4/3)^{V_p}\le4^{p+1}\). With
\(Y=A(p+1)\), using \(\log(4/3)\ge1/4\), \(\log4<2\), \(A\ge32\)
and \(e^x\ge x^2/2\), we obtain
\[
 \Pr(V_p>Y)\le e^{-(A/4-2)(p+1)}
 \le e^{-A(p+1)/8}
 \le\frac{128}{A^2(p+1)^2}\le\frac4{A(p+1)^2}.       \tag{E.vertical-tail}
\]
Together with (E.passage-bounds), this puts the point in the rectangle
\[
 |x-(j+s/4+p)|\le W:=A(p+1)\sqrt{s}+1,
 \qquad l_0<y\le l_0+Y,
\]
except with probability
\(1/(16A^2(p+1)^2)+4/(A(p+1)^2)\).
No conditioning on the realized vertical coordinate is used.

Assume \(\sqrt{s}\ge Z\) and \(p<P\). The recipe implies
\(W,Y,p\le s/64\), \(Y\le W\) and \(W\le2A(p+1)\sqrt{s}\).
The horizontal range of the rectangle, even with \(Y\) subtracted at
its left end, lies in the old triangle's top segment: use
\(\log2/\log9-1/4>1/16\) for its right end.

Consider a different triangle of size \(t'\ge u=u(p)\) meeting the
rectangle at a lattice point \((x,y)\), with left column \(a\).
Then \(x-Y<a\le x\). Otherwise \((x-Y,l_0)\) would lie in both triangles:
moving left by \(Y\) saves \(Y\log9\) of weight and moving down costs at
most \(Y\log2\). Also \(a\) is in the old top segment. Let \(b'\) be the lower endpoint of the new triangle's real vertical
section at column \(a\). Disjointness at the lattice point \((a,l_0)\)
gives \(b'>l_0\). Moving from \((x,y)\) to \((a,y)\) decreases the
triangle weight, so \(b'\le y\le l_0+Y\).

At the common integer height \(l_*=l_0+\lceil u/(2\log2)\rceil\), each
such triangle has a horizontal lattice interval starting at \(a\), of
length at least \(u/12\). Its top, at \(b'+t'/\log2\), is above
\(l_*\). Since \(u\ge4Y\log2\) and \(u\ge64\), the real section length is
\[
 \frac{(l_*-b')\log2}{\log9}
 \ge\frac{u/2-Y\log2}{\log9}
 \ge\frac{u}{4\log9}>\frac{u}{10}.
\]
 Taking an integer part loses less than one, while
\(u/10-1\ge u/12\). These lattice intervals are disjoint, so their left
columns are separated by at least \(u/32\).

All such left columns lie in an interval of length at most \(2W+Y+2\).
Each makes at most \(Y+1\) columns of the rectangle bad, because
\(x-Y<a\le x\). Thus the total number of bad columns is at most
\[
 (Y+1)\bigl(1+32(2W+Y+2)/u\bigr)\le2Y+320YW/u.
\]
This is a deterministic set of columns covering the whole rectangle.
Apply the unconditional atom bound in (E.passage-bounds), then add the
rectangle error. Since \(u(p)=H(p+1)^4\),
\[
 \Pr(\text{triangle size at }J_s+p\ge u(p))
 \le\frac{4/A+1/(16A^2)+2560A^2/H}{(p+1)^2}
       +\frac{8A(p+1)}{\sqrt{s}}.                  \tag{E.large-triangle}
\]
Use \(\sum_{r\ge1}r^{-2}\le2\),
\(\sum_{r=1}^P r\le(P+1)^2/2\) and \(\sqrt{s}\ge Z\) to get
\[
 \Pr(\exists p<P:\text{triangle size at }J_s+p\ge u(p))
 \le2(4/A+1/(16A^2)+2560A^2/H)+\delta/32<\delta.
                                                               \tag{E.large-union}
\]

### E.6. White visits and predictable cancellation

For this subsection extend all columns \(j\ge N\) as white. Write the walk
as \(z_t=(j+t,l+S_t)\). Define its first entry by
\(\sigma_1=\inf\{t\ge0:z_t\text{ is black}\}\). At an entry
\(\sigma_i<\infty\), let \(l_i\) be the top of its triangle and put
\[
 \tau_i=\inf\{t>\sigma_i:l+S_t>l_i\},\qquad
 \sigma_{i+1}=\inf\{t\ge\tau_i:z_t\text{ is black}\},
\]
with \(\inf\varnothing=\infty\). In particular, a black exit is the next
entry at that same time. The top \(l_i\) stays fixed during its crossing.
The gaps before the first entry and between each exit and the next entry
are white, and the exit times are strictly increasing.

By (E.white-exit) and the strong Markov property, the conditional expectation
of \(e^{-\mathbf1_{\{\text{white exit}\}}}\) at each entry is at most
\(1-(15/16)(1-e^{-1})\le3/4\). Iterating with the indicator that the next
entry exists gives
\[
 \Pr(R\text{ entries before }P,\ \#\text{white states before }P<K)
 \le e^K(3/4)^{R-1}\le\delta.                       \tag{E.entries}
\]
The iteration is valid even if entries cease: that path contributes zero
to the event of \(R\) entries. On the counted event, the first \(R-1\)
exit factors concern times before \(P\), and their white exits are a
subset of all white states. The final bound follows from
\(\log(4/3)\ge1/4\), so its logarithm is at most \(-16(B+1)\),
whereas \(\log(1/\delta)<4+3B\).

Now start immediately after the long crossing in E.5. Outside the event
(E.large-union), every triangle entered at time \(p<P\) has size less
than \(u(p)\). Its top is at distance less than \(u(p)/\log2<2u(p)\),
so is passed within \(u(p)+1\) pair steps. If fewer than \(K\) white
states occur, the initial gap and each later gap have length at most \(K\).
The recurrence defining \(v_i\) bounds successive entry and exit times.
Fewer than \(R\) entries with fewer than \(K\) whites cannot fill
\(P=v_R+K+2\) steps. The simultaneous quantifier over all \(p<P\) in
(E.large-union) includes the random entry times without another union bound.
Consequently
\[
 \Pr(\#\text{white states in these }P\text{ steps}<K)\le2\delta.
\]

At each white state, the next pair sum is sampled freshly and equals three
with probability \(1/4\). The state is known before that sample. The marks
at the first \(K\) white states are therefore independent Bernoulli
\((1/4)\) variables; the white extension makes these sampling times finite.
Their lower-tail bound is
\[
 \Pr(\text{fewer than }K/8\text{ marks among the first }K\text{ whites})
 \le e^{-K/32}\le\delta.
\]
For completeness, the centered log moment of a Bernoulli variable has
second derivative at most \(1/4\); integrating twice gives an upper bound
\(a^2/8\). Exponential Markov at deviation \(K/8\) gives the stated
exponent. On \(K/8\) marked whites, the product in (E.kill) is at most
\(e^{-\epsilon^2 K/4}=e^{-4(B+1)}\le\delta\).
We conclude that the auxiliary product over the \(P\) post-exit steps obeys
\[
 \mathbb E\prod_{p=0}^{P-1}
 (1-2\epsilon^2)^{\mathbf1_W(z_{J_s+p})
                  \mathbf1_{\{B_{J_s+p+1}=3\}}}
 \le4\delta=\frac1{4\cdot10^B}.                     \tag{E.postexit}
\]

### E.7. Weighted induction and the terminal event

The function \(U(j,l)\) is periodic in \(l\), with period dividing
\(2\cdot3^{n-1}\). For \(0\le m\le N\), set
\[
 D_m=\max_{N-m\le j\le N,\ l\bmod 2\cdot3^{n-1}}
                \max(N-j,1)^B U(j,l).
\]
Then \(D_0=1\), and \(D_m\ge D_{m-1}\). We prove the reverse inequality
when \(M\le m\le N\). Only the new layer \(j=N-m\) needs checking.
Put \(D=D_{m-1}\ge1\); it bounds all strictly later states with their
displayed weights.

At a white state with remaining distance \(r\ge8B/d\) whose later states
are controlled by \(D\), the kernel mass \(1-d\) gives
\[
 U(j',l')\le(1-d)D(r-1)^{-B}\le(1-d/2)Dr^{-B}.       \tag{E.white-bound}
\]
Indeed \(\log(r/(r-1))\le2/r\) and \(e^{d/4}\le1+d/2\).
This handles a white state on the new layer.

For a black state let \(s\) be its vertical distance to the triangle's top.
If \(s\le\eta m\), stop at \(J_s\). Deterministically,
\[
 J_s/m\le d/(32B),\quad m-J_s\ge m/2\ge8B/d,
 \quad(1-J_s/m)^{-B}\le1+d/8.
\]
Here \(J_s\le\eta m/2+1\) and \(m\ge64B/d\). This includes \(s=0\),
where \(J_0=1\). Discard all factors before the stop. At white exits use
(E.white-bound), and elsewhere use the ordinary later-layer bound. By
(E.white-exit),
\[
 U(j,l)\le Dm^{-B}(1+d/8)(1-15d/32)<Dm^{-B}.         \tag{E.short}
\]

If \(s>\eta m\), the recipe gives \(\sqrt{s}\ge Z\). The triangle fits
before \(N\), so \(s\log2\le m\log9\) and \(s<16m/5\).
Also \(P\le m/20\). Thus \(J_s+P>9m/10\) implies \(J_s>17m/20\),
and (E.passage) gives
\(T_s-s/2>m/10-2\ge m/20\). The binomial tail implies
\[
 \Pr(J_s+P>9m/10)\le e^{-m/640}.                    \tag{E.terminal-tail}
\]
On the complementary event all sampled states are before \(N\), and
the remaining distance is at least \(m/10\). Discard factors before
\(J_s\), use (E.postexit), and then the later-layer bound. On the
exceptional event use one. Since \(D\ge1\),
\[
 \frac{U(j,l)}{Dm^{-B}}
 \le10^B\mathbb E[\text{post-exit auxiliary product}]
                    +m^Be^{-m/640}\le\frac14+\frac14<1.         \tag{E.long}
\]
For the second term, \(\log m\le\sqrt m\) and
\(m\ge(2560(B+1))^2\) give
\(m^Be^{-m/640}\le e^{-m/1280}\le1/4\).
On the good event, every factor of the auxiliary product is before
column \(N\) and agrees with the original product. On the exceptional
event, the bound uses \(U\le1\) and its probability in (E.terminal-tail).

This proves \(D_m=D_{m-1}\) for \(m\ge M\). For \(m<M\), \(U\le1\)
gives \(D_m\le M^B\). Hence
\(U(0,0)\le M^B\max(N,1)^{-B}\). Since
\(\lfloor n/2\rfloor\ge n/3\) for \(n\ge2\), (E.primitive) follows
with \(C_B^{\rm loc}=(3M)^B\). This also completes the odd-length case.
\(\square\)

### E.8. Size of the coefficient

For \(B=6409\), the scalar definitions give
\[
 K<2^{173},\quad R<2^{175},\quad A<2^{25646},\quad
 \delta^{-1}<2^{25640},\quad H+3<2^{77000}.
\]
Writing \(w_i=v_i+1\), we have \(w_{i+1}\le(H+3)w_i^4\) and
\(w_0<2^{174}\). Therefore
\[
 \log_2 w_R<(174+77000/3)4^R<2^{15}4^R,\qquad
 \log_2(P+1)<2^{16}4^R.
\]
Also \(Z<2^{51293}(P+1)^2\), \(\eta^{-1}<2^{175}\), and
\(M<2^{102862}(P+1)^4\). The deliberately loose last prefactor bounds
every entry in (E.recipe). It follows that
\[
 \log_2 M<2^{19}4^R,\quad
 \log_2 C_{6409}^{\rm loc}<2^{33}4^R,\quad
 \log_2\log_2 C_{6409}^{\rm loc}<33+2R<2^{176}.       \tag{E.local-size}
\]

For comparison, write the coefficient in [3] as
\(C_{\rm primitive}^{\rm Maz}\). Its finite recipe is
\[
 B_0=6409,\quad E_0=2^{170},\quad L_0=2^{80},\quad
 T_0=10B_0\,2^{3E_0},\quad
 R_0=2^{E_0}(T_0+3\cdot8195+1)+1,
\]
\[
 p_0=T_0,\quad p_{i+1}=p_i+10\cdot8^{32768}(p_i+1)^3+1+T_0,
 \quad P_{\max}=p_{R_0-1},\quad P'=P_{\max}+1,\quad S_0=2^{34}P'.
                                                               \tag{M.primitiveiteration}
\]
Set
\[
 T_1=(128B_0\,2^{3E_0})^2+2,\quad
 T_2=\max\{2(T_1+L_0^2+1)+4,\ 2^{8192B_0\,2^{3E_0}},\ 2\},
\]
\[
 T_{3,s}=2+P'+P_{\max}^{10}
 +(8^{32768}(1+P_{\max})^3)^3+(100S_0)^2,
\]
\[
 T_{3,t}=(2^{38}B_0)^2+2^{38}(P'+65),\quad
 T_* =\max\{T_1,T_2,1,T_{3,s},T_{3,t}\},\quad
 C_{\rm primitive}^{\rm Maz}=(32B_0T_*)^{B_0}.        \tag{E.mazur-coefficient}
\]
This is the coefficient recipe in [3], used for the numerical comparison
below.
Put \(r=R_0-1\). Then \(r>2^{4E_0}\), \(p_0\ge2\), and
\(p_{i+1}\ge p_i^3\), so \(p_r\ge2^{3^r}\). The coefficient is at least
\(p_r\) through its \(P_{\max}^{10}\) term. With
\(L_3(x)=\log_2\log_2\log_2 x\), we obtain
\[
 L_3(C_{6409}^{\rm loc})<176,
 \qquad L_3(C_{\rm primitive}^{\rm Maz})>2^{172},
 \qquad C_{6409}^{\rm loc}<C_{\rm primitive}^{\rm Maz}.          \tag{E.coefficientcomparison}
\]
The comparison follows from the defining recurrences and their growth
bounds, without expansion of the resulting integers.

### E.9. Mixing exponents and coefficient dependence

For a primitive input of order \(\beta\), the two leading powers of the
fixed-width conversion are
\[
 a_\beta(v)=\beta-2-\tfrac12(\log2)v^2,\qquad
 q(v)-1=v\log2-1.                                  \tag{E.budget}
\]
For \(\beta>A_*+2\), both exceed \(A_*\) precisely on the intersection of
\([80,679/5]\) with
\(((A_*+1)/\log2,\sqrt{2(\beta-2-A_*)/\log2})\).
For \(\beta\le A_*+2\), the intersection is empty.
At width 80 the smallest integral \(\beta\) making both exceed six is
\[
 \beta\ge2227.                                     \tag{E.floor}
\]
At \(\beta=2227\), the smaller power is about 6.929. The order-92 seed
estimate and geometric level contraction use the stronger choice
\(\beta=6409\): the rational
width \(6749/50\) gives both powers strictly above \(2314/25\), as in
(M.exponentguards). Thus the entire Section 6 envelope and order-92 seed
estimate use the new coefficient without a change of exponent.

Lower-bound guards and quantitative sensitivity have different roles.
For any valid primitive coefficient \(C\ge1\), the adapter
\(C_6(C)=2C20^{6409}+2\) satisfies \(C_6(C)>2^{27700}\), enough for
(B.coefficientscope), \(S_{92}<C_6\), and the small-level mixing bound.
It remains strictly increasing in \(C\). In particular
\[
 F_b(C)=2^{467}b16^b(C_6(C)+1),\qquad
 V_C(n)=2^{\lceil\log_2F_b(C)\rceil}T_3(n,\lambda)
\]
are coefficient-dependent, and the envelope decreases when \(C\) decreases.
The factor \(20^{6409}\) does not erase a decrease of \(C\).
The coefficient comparison can therefore improve certified formulas;
Appendix B traces this dependence through startup, allocation, and the
density formula. The clock threshold remains \(c_0\).

## Formalization and computational data {#formalization_data}

The accompanying Phase 1 Lean development verifies common-clock and
fixed-target positive density in their existence forms, the exact
multiple-of-three criterion, a positive individual-root consequence, and
vanishing-clock-loss results for convergence to one and each admissible fixed
target. It also verifies the \(10431/1000\) clock specialization and selected
fixed-level formulas using accepted depth-eleven inputs. Seven analytic
companions extend the eleven baseline statements: the exact finite fan
allocation and its hinge dual, domination of each real-moment bound, exact
profile-density bounds for convergence to one and every admissible fixed
target at an existential paid level, and the actual reference entropy's
increment bound, finite monotone limit with explicit tail, and zero normalized
growth (including the positive-index normalized infimum). The internal proofs
also compare the profile bound with the accepted depth-eleven second and
fractional formulas. These additions do not assert the Rényi-order right
limit or the complementary-capacity comparison.

E-L1--E-L7 formalize the Appendix E primitive-decay argument, its
all-order local coefficient recipe, the order-6409 specialization, and the
canonical Section 6 consumer migration. The expanded Phase 1 proof cone uses
`LocalPrimitive.localPrimitiveDecay_order6409`; its transitive cone does not
use `explicitRenewal_numericalPrimitiveDecay` or the old `Analytic.SourceLaw`
adapter. The triple-log size bound for the local coefficient, its comparison
with the historical coefficient, and the resulting optimized-density
comparisons remain paper proofs. The other divergence-rate results,
the Rényi-order right limit, complementary capacity, deeper tables, full
optimized formulas, and amplified root families remain outside this Lean
release. Local Lean checks are distinct from independent-kernel and registry
verification; the expanded eighteen-statement package is being prepared for
those checks.

The source package provides the theorem-to-declaration correspondence,
pinned dependencies, and reproduction instructions for the finite certificates.
The reference-density tables use exact integer arithmetic, upward rounding,
and explicit positive-tail bounds. The depth-sixteen cyclic calculation
covers all \(3^{16}=43{,}046{,}721\) residues. The fractional-moment bounds
use integer square roots; the entropy values use rational logarithm enclosures.
Section 9 specifies the transfer recurrences and certificate inequalities.
The source package also contains the scalar comparisons, root-trajectory certificates,
and residue-counting calculations used in the explicit bounds.

## References

1. Terence Tao, *Almost all orbits of the Collatz map attain almost bounded
   values*, Forum of Mathematics, Pi 10 (2022), e12.
   [Corrected author preprint, v7](https://arxiv.org/abs/1909.03562v7),
   16 July 2026.
2. Terence Tao, *Equidistribution of Syracuse random variables and density
   of Collatz preimages*, 25 January 2020.
   [Author's exposition](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).
3. L. Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic
   Time*, manuscript v2.1, 6 September 2026.
   [Manuscript and supplementary material](https://www.proofatlas.ai/formalizations/positive-density-log-time-collatz/).
4. L. Mazur, *Positive Lower Density of Collatz Predecessors*,
   manuscript v1.0, 6 September 2026.
   [Manuscript and theorem statements](https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/).

5. Alex Kontorovich and Jeffrey C. Lagarias, *Stochastic Models for the
   \(3x+1\) and \(5x+1\) Problems*, in Jeffrey C. Lagarias (ed.),
   *The Ultimate Challenge: The \(3x+1\) Problem*, American Mathematical
   Society, 2010, pp. 131--188.
   [Author preprint](https://arxiv.org/abs/0910.1944).

6. Ilia Krasikov and Jeffrey C. Lagarias, *Bounds for the \(3x+1\) Problem
   using Difference Inequalities*, Acta Arithmetica 109 (2003), 237--258.
   [Author preprint](https://arxiv.org/abs/math/0205002);
   [published article](https://doi.org/10.4064/aa109-3-4).
