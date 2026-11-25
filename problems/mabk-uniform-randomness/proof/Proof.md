# Proof of Wooltorton–Brown–Colbeck Conjecture 1

**Reviewed 25 November 2026.** The independent audit identifies the domain correction at line 123. [Audit](../review/INDEPENDENT_REVIEW.md) · [Formal proof](../review/FORMALIZATION_STATUS.md)

The target is the even-party Conjecture 1 in §4.3.1, with the Bell normalization of Eq. (1). The mathematical argument below and the Lean formalization establish the same maximum. [Original paper](https://arxiv.org/abs/2308.07030v3)

## 1. Statement and notation

Let N >= 2 be even, write

$$\phi=(N-1)\pi/4,\quad Q_N=2^{(N-1)/2},\quad c_k=\cos(\phi-k\pi/2).$$

For N parties with two binary observables each, denote the full correlators by E(x), x in {0,1}^N. The paper's MABK functional is

$$M_N=2^{(1-N)/2}\sum_{x\in\{0,1\}^N}c_{|x|}E(x).$$

Its local bound is 1 and its unrestricted quantum maximum is Q_N. Define

$$d=\delta_N=\frac{\pi}{4(N+1)},\quad e=\epsilon_N=(-1)^{N/2+1},$$
$$r=\cos^{N+1}d+e\sin^{N+1}d,\quad t=\sin d\cos^N d-e\cos d\sin^N d,$$
$$s_N=\begin{cases}+1&N\equiv0,2\pmod8,\\-1&N\equiv4,6\pmod8,\end{cases}\qquad \tau=s_N t.$$

**Theorem.** Every quantum strategy satisfying $E(0\ldots0)=0$ obeys $M_N\le Q_N r$. A quantum strategy attaining equality has uniform joint outputs at that input. The maximum over strategies with uniform outputs is

$$m_N^*=Q_N r.$$

The two-party case was already established. The upper bound in §§2–5 treats even $N\ge4$. Section 6 identifies the value with the original published expression for every even $N$. Proposition 2 and Lemma 5 of the paper address device-independent certification. [Bipartite result](https://arxiv.org/abs/2205.00124)

## 2. Reduction from arbitrary quantum strategies to a torus disk bound

Uniformity gives E(0)=sum_a (-1)^|a| 2^(-N)=0, since there are equally many even and odd strings. For an arbitrary quantum strategy, first consider binary projective observables A_j(0), A_j(1), which are self-adjoint unitaries. Operators of different parties commute (in particular in the tensor-product model). Put

$$A_0=\prod_j A_j(0),\qquad U_j=A_j(0)A_j(1).$$

Each U_j is unitary and the U_j commute with one another and with each other's adjoints. Define the symmetric multi-affine polynomial

$$P(z_1,\ldots,z_N)=2^{1-N}\sum_{S\subseteq\{1,\ldots,N\}} c_{|S|}\prod_{j\in S}z_j.$$

By the ordering A_j(0)U_j=A_j(1), the normalized Bell operator is B=A_0 P(U), with expectation M_N/Q_N. For real tau,

$$B-\tau A_0=A_0(P(U)-\tau I).$$

Since A_0 is unitary, the operator norm equals ||P(U)-tau I||. Joint continuous functional calculus for commuting unitaries bounds this by max_{|z_j|=1}|P(z)-tau|. For mixed states as well as pure states, absolute expectation of the self-adjoint operator B-tau A_0 is bounded by its operator norm. Therefore

$$|M_N|/Q_N\le \max_{|z_j|=1}|P(z)-\tau|$$

whenever E(0)=0. (This applies to arbitrary local Hilbert dimensions in the usual bounded-operator model.)

For binary POVMs, each observable is a self-adjoint contraction H=A(0) or A(1). On the same enlarged local space Hloc ⊕ Hloc, with common embedding V:v↦(v,0), replace each contraction X by the self-adjoint unitary

$$\widetilde X=\begin{pmatrix}X&\sqrt{I-X^2}\\\sqrt{I-X^2}&-X\end{pmatrix}.$$

The two choices of X need not commute. Each has compression V* Xtilde V=X; applying the tensor product of the local embeddings to the state preserves every measured joint probability and correlator because only one measurement per party occurs per run. This proves the upper-bound reduction for the tensor-product quantum model, including mixed states. The commuting-operator variant for contractions, if desired, requires a separately stated local ancilla dilation argument; the projective commuting-unitary proof above is immediate.

It remains to show the explicit disk bound

$$\max_{|z_j|=1}|P(z)-\tau|\le r.\tag{D}$$

## 3. Symmetric multi-affine maximum on the diagonal

**Lemma.** If F is a symmetric multi-affine complex polynomial in N variables, then its maximum modulus on the unit torus equals the maximum modulus of its diagonal restriction on the unit circle.

**Proof.** The torus is compact. Among maximizers of |F| choose one maximizing the continuous secondary objective |sum_j z_j|². If two coordinates z_i,z_j differ, choose a unit complex number u and real v so that z_i=u exp(iv), z_j=u exp(-iv). Their product is u² and their sum is 2u cos v with -1<cos v<1 (the endpoints would make them equal). With the other coordinates fixed, symmetry and multi-affinity imply F=A+B(z_i+z_j)+C z_i z_j for some complex A,B,C. As w varies in [-1,1], the replacement pair u exp(i arccos w), u exp(-i arccos w) stays on the torus, and F(w)=A+Cu²+2Buw is affine in w. If B≠0, strict convexity of squared modulus along a nonconstant line segment implies an endpoint has strictly larger |F|² than the interior w=cos v, a contradiction. If B=0, the primary objective is constant along the segment. The squared secondary objective |sum_{k≠i,j}z_k+2uw|² is strictly convex because |u|=1. One endpoint strictly improves it, another contradiction. Therefore all coordinates are equal. The proof also covers antipodal coordinates and constant F. QED.

Apply this to F=P-tau. It suffices to prove (D) for z_1=...=z_N=z on the unit circle.

## 4. Diagonal polynomial and residue classes

The binomial theorem gives the diagonal

$$W(z)=P(z,\ldots,z)=2^{-N}\left[e^{i\phi}(1-iz)^N+e^{-i\phi}(1+iz)^N\right].$$

For z=exp(i(pi/2+2x)), -pi/4<=x<=pi/4 (upper semicircle), the evenness of N gives

$$W(z)=e^{i(\phi+Nx)}(\cos^N x+i\sin^N x).\tag{1}$$

Indeed 1-iz=2 exp(ix) cos x, 1+iz=-2i exp(ix) sin x, and exp(-2i phi)(-i)^N=i. The lower semicircle is obtained by conjugation since W has real coefficients. The proposed center tau is real, so conjugation preserves distance to it.

Define the canonical curve

$$C(x)=e^{i(\pi/4+Nx)}(\cos^N x+ie\sin^N x).$$

Here is the full reduction table for the upper semicircle. In the table, w(x)=W(exp(i(pi/2+2x))).

| N mod 8 | e | Identity | tau | Angle theta* giving Im W(exp(i theta*))=r |
|---|---:|---|---:|---|
| 0 | -1 | w(-x)=conj C(x) | t | 3pi/2+2d |
| 2 | +1 | w(x)=C(x) | t | pi/2+2d |
| 4 | -1 | w(-x)=-conj C(x) | -t | pi/2-2d |
| 6 | +1 | w(x)=-C(x) | -t | 3pi/2-2d |

These equalities follow from (1), periodicity of phi modulo 2pi, and evenness of cos^N and sin^N. In particular, each transformation preserves distance when the center is transformed by the same isometry; the argument x still runs over the entire interval. Hence (D) follows from

$$|C(x)-t|\le r,\quad -\pi/4\le x\le\pi/4.\tag{2}$$

At x=d, (N+1)d=pi/4, hence pi/4+Nd=pi/2-d, giving directly C(d)=t+ir.

## 5. Global canonical disk inequality (N even, N>=4)

All estimates below are uniform in N. They require no numerical computation. The proof uses the derivative sign near the contact point and a strict bound on the rest of the curve.

### 5.1 Basic bounds and elementary estimates

Set k=Nd². By 3<pi<22/7, pi²<10, N/(N+1)>=4/5, N/(N+1)²<=4/25, and N+1>=5,

$$0<d<1/6,\quad Nd>3/5,\quad k<1/10,\quad (N+1)d^2<1/8.\tag{3}$$

In particular 3d<1/2<pi/4. We use on 0<=y<=1/2:

$$y-y^3/6\le\sin y\le y,\quad 1-y^2/2\le\cos y\le e^{-y^2/2}.$$

The lower bounds follow by Taylor or integration of the elementary inequalities. For the upper cosine bound, (log cos y)'=-tan y<=-y because (tan y-y)'=tan² y>=0. The Bernoulli bound (1-u)^j>=1-ju for integer j>=1 and 0<=u<=1 gives cos^j y>=1-j y²/2. Also exp(-a)<=1-a+a²/2 for a>=0, e.g. by two integrations of exp(-a)<=1. These standard facts must be instantiated in the formal proof, not assumed as new axioms.

For eta in {-1,+1} put

$$f_\eta(y)=\sin y\cos^N y-\eta\cos y\sin^N y.$$

Then t=f_e(d). Since N>=4 and d<1/6,

$$f_\eta(d)\ge d(1-d^2/6)(1-k/2)-d^N$$
$$>d\left[(1-1/216)(19/20)-1/216\right]>(9/10)d,$$

and f_eta(d)<=d+d^N< (101/100)d, since d^(N-1)<=1/216. Thus 0<t<(101/100)d. In addition, for 0<=y<=d, f_eta(y)>=0 because cos y>=sin y>=0 and sin y cos^N y>=cos y sin^N y (factor sin y cos y).

### 5.2 Uniform derivative bounds for f_eta

Differentiation gives

$$f_\eta'(y)=\cos^{N-1}y(1-(N+1)\sin^2 y)-\eta\sin^{N-1}y(N-(N+1)\sin^2 y).$$

On 0<=y<=2d, cos^{N-1}y>=1-2k>4/5, and 1-(N+1)sin² y>=1-4(N+1)d²>1/2. The magnitude of the second term is bounded by N(1/3)^(N-1)<=4/27; the factor N-(N+1)sin² y lies between 0 and N. The bound for N follows by comparing successive integers (j+1)/(3j)<1 for j>=4. Therefore f_eta'(y)>(4/5)(1/2)-4/27>0.

On 0<=y<=d, use the sharper bounds cos^{N-1}y>19/20, 1-(N+1)sin² y>7/8 and N(1/6)^(N-1)<=4/216. This yields

$$f_\eta'(y)>(19/20)(7/8)-4/216>3/4.\tag{4}$$

Consequently f_e(x)<=t-(3/4)(d-x) for 0<=x<=d by the mean value theorem; f_e(y)>=t on [d,2d]. For g=f_{-e}, on [d,2d], g(y)>=g(d)>(9/10)d>(3/4)t.

### 5.3 Intermediate interval 2d<=y<=3d

Let h(y)=sin y cos^N y. Its derivative is cos^{N-1}y(1-(N+1)sin² y), with at most one sign change from positive to negative on [0,pi/4]. Its minimum on [2d,3d] thus occurs at an endpoint. Explicitly,

$$h(2d)\ge 2d(1-4d^2/6)(1-2k)>2d(1-1/54)(4/5)>(3/2)d,$$
$$h(3d)\ge 3d(1-9d^2/6)(1-9k/2)>3d(1-1/24)(11/20)>(3/2)d.$$

Also tan y<= (1/2)/(1-1/8)=4/7<3/5. Because f_eta(y)=h(y)(1-eta tan^{N-1} y),

$$f_\eta(y)>(3/2)d[1-(3/5)^3]=(147/125)d>t.\tag{5}$$

This applies to both signs eta.

### 5.4 Derivative signs of squared distance

Set D(x)=|C(x)-t|², alpha=pi/4+(N+1)x and R(x)=cos^{N-1}x+e sin^{N-1}x. Differentiation and taking the real part gives

$$C'(x)=iN e^{i\alpha}R(x),$$
$$D'(x)=2NR(x)[-\sin x\cos^N x+e\cos x\sin^N x+t\sin\alpha].\tag{6}$$

For verification, 2 Re(C'(x) conj(C(x)-t)) gives (6), since Re(i exp(ix)(cos^N x-i e sin^N x))=-sin x cos^N x+e cos x sin^N x. On |x|<=pi/4, R(x)>=0 since cos x>=|sin x|. For x>=0 the bracket is -f_e(x)+t sin alpha; for x<0 it is f_{-e}(-x)+t sin alpha, by even N.

Write S(x)=sin alpha. Since (N+1)d=pi/4, its argument is pi/4+(pi/4)x/d. We check each interval:

| Interval | Bound and sign of bracket |
|---|---|
| [-3d,-2d] | g(-x)>=t by (5), S>=-1; nonnegative. |
| [-2d,-d] | g(-x)>3t/4 by §5.2; S>=-sqrt(2)/2>=-3/4; nonnegative. |
| [-d,0] | g(-x)>=0, S>=0; nonnegative (at x=0 the other formula agrees). |
| [0,d] | S>=1-(d-x)/(2d) by concavity of sin on [pi/4,pi/2] and sin(pi/4)>=1/2. By (4), bracket >= (3/4-t/(2d))(d-x)>=0. |
| [d,2d] | f_e(x)>=t, S<=1; nonpositive. |
| [2d,3d] | f_e(x)>t by (5), S<=1; nonpositive. |

By (6) and R>=0, D is nondecreasing on [-3d,d] and nonincreasing on [d,3d]. Thus D(x)<=D(d)=r² throughout [-3d,3d]. Here r>0: cos d>sin d>=0.

### 5.5 Outside the intermediate interval

The even function |C(x)|²=cos^{2N}x+sin^{2N}x is nonincreasing for x in [0,pi/4]. Its derivative there is 2N sin x cos x (sin^{2N-2}x-cos^{2N-2}x)<=0. For 3d<=|x|<=pi/4, therefore

$$|C(x)|\le \sqrt{\cos^{2N}(3d)+\sin^{2N}(3d)}\le \cos^N(3d)+\sin^N(3d).$$

By (3), a=(9/2)k<9/20. Then

$$\cos^N(3d)\le e^{-a}\le 1-a+a^2/2\le1-(13/4)k,$$

because (9/2)(1-9/40)=279/80>13/4. Also, since 3d<1/2 and N>=4,

$$\sin^N(3d)\le(3d)^4=81d^4<(3/8)d.$$

Finally, regardless of e,

$$r\ge1-(N+1)d^2/2-d^{N+1}$$
$$=1-(\pi/8)d-d^{N+1}>1-(41/100)d,$$

using pi/8<11/28 and d^N<=1/1296. It follows that

$$|C(x)-t|\le |C(x)|+t\le1-(13/4)k+(3/8+101/100)d$$
$$<1-(113/200)d<1-(41/100)d<r,$$

where k=Nd²>(3/5)d and 13/4*3/5-3/8-101/100=113/200. Combined with the central result this proves (2), and hence (D), for all even N>=4. Equality occurs at the transformed point corresponding to x=d.

## 6. Saturation, uniform probability, and match with published m_N*

Use the N-qubit GHZ state (|0...0>+i|1...1>)/sqrt(2). Each party measures A_j(0)=X and A_j(1)=cos(theta) X+sin(theta) Y, with standard Pauli Y. For the input x of Hamming weight k, the tensor product flips |0...0> to exp(i k theta)|1...1> and |1...1> to exp(-i k theta)|0...0>. Its expectation in the chosen state is sin(k theta). Therefore M_N/Q_N=Im W(exp(i theta)).

At all-zero input, measuring the X basis yields for the string a the amplitude 2^{-(N+1)/2}(1+i(-1)^|a|), whose squared modulus equals 2^{-N} for every string. This demonstrates true uniformity, not merely E(0)=0.

Use theta* from the table in §4. In each residue class Im W(exp(i theta*))=r, since C(d)=t+ir and conjugation/sign act as described in the table. These angles equal the published Eq. (25) angles 2pi t_N/(N+1) in Eq. (26), as follows:

| N mod 8 | theta* | (N+1)theta*/(2pi) |
|---|---|---|
| 0 | 3pi/2+2d | 3N/4+1 |
| 2 | pi/2+2d | N/4+1/2 |
| 4 | pi/2-2d | N/4 |
| 6 | 3pi/2-2d | 3N/4+1/2 |

This identifies $Q_N r$ with Eq. (27) for every even $N\ge2$. For $N=2$ the formula gives $3\sqrt{3}/4$, in agreement with the earlier bipartite result and Appendix C.4.

Combining §§2–5 with this attaining strategy proves Conjecture 1 for every even $N\ge4$. The independent review gives a separate proof for $N=2$ and documents the available priority evidence. [Review](../review/INDEPENDENT_REVIEW.md)

## 7. Formal proof decomposition

The submitted Lean file contained the chord identity (§3), derivative sign certificates (§5.4), an outer rational gap (§5.5), and a conditional monotonicity theorem. The reviewed project proves global symmetrization, both disk claims, the quantum reduction, saturation, and their composition into the published conjecture. Its proof of the central disk uses a separate half-turn argument. See `review/FORMALIZATION_STATUS.md`.

The submitted file also outlined a finite phase-mixture route. The completed formal proof derives its operator bound by applying the Gelfand transform to the closed commutative algebra generated by local relative unitaries. See `MABKCore/Quantum.lean`.
