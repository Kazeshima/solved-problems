# Contextuality of the real Pauli quadric

## 1. The signed incidence problem

Put \(d=2^n\), \(E=\mathbb F_2^n\), \(V=E\oplus E\), \(q(a,b)=a\cdot b\) and \(B(p,r)=q(p+r)+q(p)+q(r)\). The \(n\) independent hyperbolic pairs give \(q\) plus type. Over \(\mathbb F_2\) a nonzero singular vector represents exactly one projective point. The quadric has point set \(Q=\{p\ne0:q(p)=0\}\). Its projective lines are precisely the unordered sets \(\{p,r,p+r\}\) of three distinct members of \(Q\). Singularity of all three is equivalent to orthogonality of the first two singular members.

In the real computational basis let \(P(a,b)e_x=(-1)^{b\cdot x}e_{x+a}\). Write \(r=(c,h)\). Then
\[
 P(p)P(r)=(-1)^{b\cdot c}P(p+r),\qquad
 P(p)^T=(-1)^{q(p)}P(p).
\]
Thus the symmetric labels are exactly the singular ones, including the identity at zero. The commutator sign is \((-1)^{B(p,r)}\), and on a line the operator product is \(\epsilon_\ell I\) with \(\epsilon_\ell=(-1)^{b\cdot c}\) in every order. The tensor-Hermitian convention replaces each \(XZ\) factor by \(Y=iXZ\). With an even number \(k\) of such factors its representative is \((-1)^{k/2}P(p)\). Multiplying an assigned sign by the same factor at that point gives a bijection preserving each violated line. Other hyperbolic quadrics in the Pauli space are related by symplectic label maps lifted by Clifford conjugation and this same rephasing. This is the signed problem defined by Li, Gupta and Ganesh. [Pinned manuscript, definitions and Clifford transport](https://github.com/BrianLi009/four-qubit-hyperbolic-quadric/blob/44a37dbd55029eec23f8c15f071e263984635444/main.tex)

An assignment \(s:Q\to\{\pm1\}\) has \(N(s)\) violations, namely those lines with \(\epsilon_\ell\prod_{p\in\ell}s_p=-1\). Write \(m=|Q|,\ L=|\mathcal L|,\ D=\min_s N(s)\). All functions on \(Q\) are permitted. Extending them arbitrarily off \(Q\) leaves \(D\) unchanged. Counts of distinct assignments below always refer to restrictions to \(Q\).

## 2. Counts by character sums

Write \(\chi(t)=(-1)^t\). Translation by a vector with \(b\cdot x=1\) proves \(\sum_x\chi(b\cdot x)=d\,1_{b=0}\). Hence \(\sum_{p\in V}\chi(q(p))=d\) and \(2(m+1)=d^2+d\). For fixed \(p\in Q\), count all \(r\in V\) such that \(q(r)=q(r+p)=0\). Four times this count is
\[
 \sum_r(1+\chi(q(r)))(1+\chi(q(r+p)))=d^2+2d .
\]
The remaining character sums to zero since \(B(r,p)\) is a nonzero linear functional. Removing \(r=0,p\) leaves \((d-2)(d+4)/4\) ordered partners. Each unordered line occurs six times. Therefore
\[
 m=(d-1)(d+2)/2,\qquad L=(d-1)(d-2)(d+2)(d+4)/48 .
\]
These give nine points and six lines at \(n=2\). Its grid has degree one.

## 3. A sharp uniform bound from three moments

A nonzero translation has zero matrix trace. For a zero translation the trace is the character sum in §2. It follows that \(\operatorname{tr}(P(p)P(r))=d\,1_{p=r}\) on singular labels. With the identity there are \(d(d+1)/2\) mutually orthogonal symmetric matrices, hence a basis of all real symmetric matrices. For \(A=\sum_{p\in Q}s_pP(p)\),
\[
 \operatorname{tr} A=0,\quad \operatorname{tr} A^2=dm,\quad
 \operatorname{tr} A^3=6d\,(L-2N(s)).
\]
Indeed the only triples surviving in the third trace have label sum zero. Their three labels are distinct since zero was removed. They form precisely the lines in §1. Each of the six orderings yields \(d\,\epsilon_\ell\prod s_p\).

Let \(a=\sqrt{(d+2)/2}\). The eigenvalues \(x_i\) of \(A\) have zero sum and squared norm \(d(d-1)a^2\). Cauchy–Schwarz on the other \(d-1\) coordinates gives \(x_i^2\le(d-1)(d(d-1)a^2-x_i^2)\). Thus \(x_i\le(d-1)a\). The sum of \(((d-1)a-x_i)(x_i+a)^2\) is nonnegative. Expanding and substituting the first two moments gives
\[
 \sum_i x_i^3 \le d(d-1)(d-2)a^3 .
\]
Equality for \(d>2\) forces the eigenvalues to be \((d-1)a,-a,\ldots,-a\), and that list attains equality. This is the sharp zero-mean third-moment inequality, often called Okumura's lemma. [Okumura](https://doi.org/10.2307/2373587)

Inserting the cubic trace and the value of \(L\) yields
\[
 \frac12-\frac{D}{L}\le\frac{(d-1)(d-2)a^3}{12L}
 =\frac{\sqrt{2(d+2)}}{d+4}.
\]
Negating every assigned sign interchanges satisfied and violated lines, since every line has three points. One member of any opposite pair has at most \(L/2\) violations. This also follows by averaging independent signs. The squared error bound is at most \(2/d\), so \(D/L\to1/2\). This answers the limit part of revised open problem 4.

### Equality can occur only at four qubits

The matrix \(A\) has integer entries. Equality gives characteristic roots \((d-1)a\) once and \(-a\) with multiplicity \(d-1\). If \(a=\sqrt{2^{n-1}+1}\) were irrational, the rational characteristic polynomial would also have \(+a\) as a root, contradicting this list for \(d\ge4\). Thus \(a=k\) is an odd integer, and \((k-1)(k+1)=2^{n-1}\). The two positive even factors differ by two, forcing \(2,4\). Hence \(n=4\). Section 5 supplies equality there.

Jonah's Theorem 6 gives the explicit spectral excess \(m^{3/2}(d-2)/(6\sqrt{d-1})\). Dividing it by \(2L\) is exactly the displayed coefficient. Equality for \(d\ge4\) forces \(a\) rational since \(6(L-2D)=(d-1)(d-2)a^3\) and \(a^2\) is an integer. Thus \(a\) is integral and \((a-1)(a+1)=2^{n-1}\); the two factors are 2 and 4. Section 5 gives the unique saturating rank. Both the general bound and this saturation conclusion were already public. [Jonah, Theorems 6 and 8](https://doi.org/10.5281/zenodo.23538829)

## 4. The same finite bound from Jonah's section theorem

This independently addresses implicit priority. Put \(h=d/2\). Fix a point off the quadric and its perpendicular section \(S\simeq W(2n-3,2)\). All remaining lines have two points outside and one inside. There are \(h(h+1)\) outside points. The section has \(h^2-1\) points, each with \(h^2/2-2\) ordered partners, hence \(L_S=(h^2-1)(h^2-4)/12\). Subtracting from \(L\) gives \(L_O=h(h^2-1)(h+2)/4\) outside lines.

For fixed section signs, Jonah's signed adjacency \(\Lambda\) on the outside points has largest eigenvalue \(\mu_1\), that of the signed sum \(A'\) of all \(h^2-1\) nonidentity Hermitian Paulis in dimension \(h\). The signed sum on outside lines is \(X^T\Lambda X/2\). Orthogonality gives \(\operatorname{tr} A'=0\) and \(\operatorname{tr}((A')^2)=h(h^2-1)\). Cauchy–Schwarz on the other eigenvalues gives \(\mu_1\le(h-1)\sqrt{h+1}\). The signed bias per outside line is at most
\[
 \frac{h(h+1)(h-1)\sqrt{h+1}}{2L_O}
 =\frac{2\sqrt{h+1}}{h+2}.
\]
The full orthogonal group acts transitively on totally singular lines by Witt extension. It also permutes the outside-section family. Consequently each line appears outside equally often, with positive multiplicity as \(L_O>0\). Applying the bound to a fixed global assignment in every section gives the same bound on its global bias. Dividing by two reproduces the precise bound of §3 for every \(n\ge2\). Theorem 2 of the October deposit provides the substantive spectral input. [Jonah, Theorem 2 and Corollary 5](https://doi.org/10.5281/zenodo.23510634)

## 5. Four-qubit spectral rigidity and a witness

Here \(m=135,\ L=1575,\ a=3\). The bound gives \(N\ge315\). At equality the spectral theorem gives \(A=48\psi\psi^T-3I\) for a real unit vector unique up to sign. Taking the trace against a nonidentity symmetric \(P\) gives \(\psi^TP\psi=s_P/3\). Conversely a real unit vector with those expectations gives this \(A\), by the orthogonal basis of §3, hence exactly 315 violations.

Take \(v=(3,-1,\ldots,-1)\), \(\psi=v/\sqrt{24}\). For each singular nonidentity label,
\[
  v^TP(a,b)v=16\,1_{a=0}+16\,1_{b=0}-8 .
\]
Expand \(v_x=4\,1_{x=0}-1\); the cross terms have phases 1 at \(x=0,a\). Thus the assignment \(s_*(a,b)=(-1)^{[a\ne0,\ b\ne0]}\) attains equality. The assigned operator is \(2vv^T-3I\). For comparison, directly in the normalized basis, the rank-one projector has Pauli expansion \(d^{-1}(I+\sum_{p\in Q}\langle P(p)\rangle P(p))\).

## 6. Classification of the real equality states

Set \(K=(A+3I)/2=24\psi\psi^T\), \(k_x=K_{xx}\). Every diagonal entry of \(A\) is a sum of 15 signs. Each off-diagonal entry is a sum of eight signs, from the \(b\) perpendicular to its nonzero row-column difference. Thus \(K\) is integral. Its trace is 24. By Walsh orthogonality on the diagonal,
\(\sum_x k_x^2=16(3^2+15)/4=96\).
Each \(k_x\) is nonnegative and at most 9. Since \(k_xk_y=K_{xy}^2\), prime valuations of all positive \(k_x\) agree modulo two. Their common squarefree part \(c\) obeys \(c^2\mid96\), so \(c=1\) or \(2\). For \(c=1\), writing \(m_j\) for occurrences of \(j\), subtraction of the two moments gives \(m_4+6m_9=6\). For \(c=2\) the two positive values are 2 and 8 and the two equations give their multiplicities. The complete list is

| Type | Nonzero squared entries in \(\sqrt{24}\psi\) | Zeros |
|---|---|---:|
| H | \(9^1,1^{15}\) | 0 |
| M | \(8^1,2^8\) | 7 |
| S | \(4^6\) | 10 |

Here superscripts denote multiplicities. Translations, invertible binary coordinate maps, single Hadamards, and diagonal phases given by binary quadratic functions are real Clifford gates. Translations and coordinate changes permute the computational basis. Direct conjugation interchanges \(X,Z\) for a Hadamard. The phase-gate calculation appears below. These operations permute the symmetric Paulis up to signs, preserving flatness.

Fix a nonzero direction \(e\). Choose one complement to its span. The Hadamard along \(e\) applies \((u,v)\mapsto((u+v)/\sqrt2,(u-v)/\sqrt2)\) within each ordered pair from that complement. It is an involution. For an S vector, the difference of two occupied positions leads to an entry of squared magnitude 8. For an M vector, the difference between the heavy site and a light site leads to a 9. Thus every equality state can be brought to H.

Translate the heavy site to zero and choose its sign positive. Write the other entries of \(\sqrt{24}\psi\) as \((-1)^{t(x)}\) and put \(t(0)=0\). For \(e\ne0\), let \(w([x])=24(-1)^{t(e)}\psi_x\psi_{x+e}\) on the eight cosets modulo \(e\). Its value at zero is 3 and all others have modulus one. Its Walsh coefficients have modulus 4, since the Pauli expectation at \((e,b)\) is \((-1)^{t(e)}\widehat w(b)/12\) for \(b\perp e\). Their sum is \(8w(0)=24\), giving seven \(+4\)'s and one \(-4\), say at \(b_e\). Inversion gives \(w([x])=4\,1_{[x]=0}-(-1)^{b_e\cdot x}\).

Define \(f(x)=t(x)+[x\ne0]\). Reading the preceding identity at \(x\notin\{0,e\}\), and then checking \(0,e\) using \(b_e\perp e\), gives
\[
 f(e+x)+f(e)+f(x)=b_e\cdot x .
\]
This holds also at \(e=0\) with \(b_0=0\). Symmetry of the left side makes the right side bilinear, since each row is linear. The bilinear form is alternating. Subtract \(\sum_{i<j}(b_{e_i}\cdot e_j)x_ix_j\) from \(f\) to leave a linear function. Thus \(f\) is quadratic of degree at most two with zero constant. The diagonal gate \(D_f\) conjugates \(P(e,b)\) to \((-1)^{f(e)}P(e,b+b_e)\). It sends the H state to \(\psi_*\). Conversely every such \(f\) acting on \(\psi_*\) gives an H state. This proves transitivity on all optimal projectors without an enumeration.

For each heavy position there are \(2^{4+6}\) distinct quadratic phases with zero constant. This gives \(H=16\,384\) projective states. Use one fixed Hadamard per direction. All 15 directions send H to M, and exactly eight send M to H. Its seven other directions pair the heavy site with zero, yielding a 4 and hence type S. Every direction sends S to M. Indeed if it paired each occupied site with zero, all positive squared entries after the transform would be 2, contrary to the list. Involutivity now gives \(15H=8M,\ 7M=15S\); thus \(M=30\,720,\ S=14\,336\). Projectors and optimal assignments are in bijection by §5. Their number is **61,440**.

If two assignments have the same violated lines, their pointwise ratio \((-1)^{u(p)}\) has zero binary sum on each line. Set \(u(0)=0\). On each pure \(X\)- or \(Z\)-space this is precisely additivity, including coincident or zero arguments. For a mixed singular point the pure pair \((a,0),(0,b)\) lies on its line, forcing \(u(a,b)=u(a,0)+u(0,b)\). Every gauge is therefore the restriction of a linear form on \(V\), and all \(2^8\) forms give different gauges. There are \(61\,440/256=\mathbf{240}\) distinct violated sets. A Clifford maps one set to the next since conjugation simultaneously changes observable and assignment signs. Orthogonal relabellings preserve the signed problem up to rephasing: for an isometry \(T\), the difference \(b\cdot c+(Tp)_Z\cdot(Tr)_X\) is a symmetric alternating bilinear form, hence the polarization of a binary quadratic phase. This also establishes a single orbit for the full orthogonal group.

## 7. The incidence isomorphism

Let \(W=\mathbb F_2^3\oplus\mathbb F_2^3\) with alternating form \(x\cdot z'+z\cdot x'\). The points of \(DW(5,2)\) are its three-dimensional totally isotropic subspaces; a line is the pencil of three through a fixed two-dimensional isotropic subspace. For a row basis \([X|Z]\) take the eight transversal minors \(p_S\), choosing column \(Z_i\) in position \(i\in S\) and \(X_i\) otherwise. Basis changes have determinant one. Pack the minors as \(a=(p_\emptyset,p_{23},p_{13},p_{12}), b=(p_{123},p_1,p_2,p_3)\). This is the known binary principal-minor embedding. [Lévay, Planat and Saniga](https://arxiv.org/abs/1305.5689) · [Holweck, Saniga and Lévay](https://arxiv.org/abs/1311.2408)

A transversal minor is nonzero on every Lagrangian. Choose a nonzero coordinate functional on it, swapping the pair to call it \(X_i\). Its kernel projects injectively to the other pairs: a vector lost under projection could only have a \(Z_i\) component, contradicting orthogonality to a vector with \(X_i=1\). The projected kernel is isotropic of dimension one less. Induction and expansion along \(X_i\) prove the assertion. Each coordinate swap permutes complementary pairs of minors and either preserves all their parities or exchanges the even and odd blocks globally. It acts by the **same** coordinate permutation in both packed blocks, possibly followed by total block interchange. It preserves \(q\), the mixed-point indicator, and \(b\cdot c\) on commuting pairs because there \(b\cdot c=a\cdot h\).

In the chart \(p_\emptyset=1\) row reduction gives \([I|M]\) with \(M\) symmetric. Write \(d_i=M_{ii}\), \(e=(e_{23},e_{13},e_{12})\) where \(e_{ij}=d_id_j+M_{ij}\). Expansion of the determinant gives \(\det M=d\cdot e\). The chart is therefore \(a=(1,e), b=(d\cdot e,d)\). Its coordinates recover \(M\). Two equal packed vectors share a nonzero minor, so chart injectivity gives global injectivity. The number of Lagrangians obeys \(T_j(2^j-1)=(2^{2j}-1)T_{j-1}\) on counting a nonzero vector in a Lagrangian and passing to its symplectic quotient. Thus \(T_3=3\cdot5\cdot9=135\), proving surjectivity onto the quadric.

The three images of a pencil sum to zero by multilinearity in the third row, with a common first two rows. Some minor coordinate is nonzero, and is one on precisely two images. Move that minor to the empty chart. The two matrices \(M,N\) there differ by rank one, since their graphs intersect in dimension two. A symmetric binary rank-one matrix is \(uu^T\) for \(u\ne0\). Adding it gives \(d'=d+u\), \(e'_{ij}=e_{ij}+d_i u_j+d_j u_i\). Consequently the ordered Pauli phase exponent is \(b\cdot c=d\cdot(e+e')=0\), because each term appears twice. For \(g=[a\ne0,\ b\ne0]\) the three indicators are \([d\ne0]\), \([d\ne u]\), \([d\notin\{0,u\}]\). For the last, the second block has tail \(u\), while the first has tail \(d\wedge u\). Their parity is one in each case. Hence every pencil gives a violation for \(s_*\). Each Lagrangian contains seven 2-spaces and each pencil has three points. There are \(135\cdot7/3=315\) pencils, exactly the number of violations. Distinct pencils have different triples because two members determine their intersection. Clifford transport proves the incidence statement for every optimum. Coupled with the published doily optimality equivalence this answers the conceptual question on its stated class of realizable assignments.

## 8. A matching order for the gap

Here is an additional argument developed during the audit. It applies simultaneously to every hyperbolic Pauli line. Use a real standard Gaussian vector \(G\in\mathbb R^d\). Given \(G\), draw the signs independently with means \(\sin(tG^TPG/\sqrt d)\) for a fixed \(t>0\). This defines an ordinary distribution on deterministic, context-independent assignments. The optimum signed bias is at least the mean bias.

On a line replace the third observable by \(R=PQ\); the sine is odd, so this absorbs the line sign. The four joint eigenspaces of \(P,Q\) each have dimension \(d/4\): the four spectral projectors are \((I\pm P)(I\pm Q)/4\), and all three nonidentity traces vanish. Write \(U,V,W\) for the corresponding three quadratic forms scaled by \(t/\sqrt d\). Each one-minus combination among \(U,V,W\) has the distribution of \(-(U+V+W)\), by the joint spectrum. Product-to-sum gives
\[
 \mathbb E(\sin U\sin V\sin W)=-\operatorname{Im}\!\left[
 (1-6it/\sqrt d)^{-d/8}(1+2it/\sqrt d)^{-3d/8}\right].
\]
Indeed the sum has coefficient \(3\) on one joint space and \(-1\) on each of the other three, and independent squared Gaussian coordinates have characteristic function \((1-2iz)^{-1/2}\). Powers use the continuous branch at zero. This is an exact expression for each \(d\).

The logarithm is \(-3t^2-8it^3/\sqrt d+O_t(d^{-1})\); the fourth-order term is real and the next imaginary term has order \(d^{-3/2}\). The convergent logarithm series for fixed \(t\) justifies these errors for all sufficiently large \(d\). The expected signed bias is \(8t^3 e^{-3t^2}/\sqrt d+O_t(d^{-3/2})\). Setting \(t=1/\sqrt2\) gives
\[
 \sqrt2\,e^{-3/2}\ \le\ \liminf_{n\to\infty}\sqrt d\,(1/2-D/L)
 \le \limsup_{n\to\infty}\sqrt d\,(1/2-D/L)\le\sqrt2 .
\]
Thus the **order** \(2^{-n/2}\) is optimal. The leading optimal constant and existence of a rescaled limit are open here. This strengthening is proved on paper; the Lean endpoint concerns the original bound and limit.

## 9. Five qubits

For \(Q^+(9,2)\), the independently counted mixed-point witness has \(6\,975\) violations among \(23\,715\) lines. Every line belongs to 112 of its 496 off-point sections, each a signed \(W(7,2)\). With \(D(W(7,2))=1\,575\), incidence counting yields \(112D\ge496\cdot1\,575\), achieving the witness. In \(W(7,2)\) every line belongs to 24 of 120 elliptic quadrics with degree 315, giving \(24D\ge120\cdot315\), again achieved. The difficult elliptic lower bound uses a finite census and 42 exact certificates in Jonah's proof. Thus the five-qubit answer depends on finite computer-assisted input. The uniform cubic lower bound alone gives only \(\lceil23\,715(1/2-\sqrt{68}/36)\rceil\). [Jonah, Theorem 6 and §4](https://doi.org/10.5281/zenodo.23510634) · [Li, Gupta and Ganesh, revised proof](https://github.com/BrianLi009/four-qubit-hyperbolic-quadric/blob/44a37dbd55029eec23f8c15f071e263984635444/main.tex)

### Finite verification of the elliptic bound

Write the score of an assignment as its number of violated lines. Each line of the four-qubit elliptic quadric lies in 40 of its 136 sections. Consequently, any assignment with fewer than 315 violations has a three-qubit section with at most 92. Each line of that section belongs to 15 of its 63 hyperplanes. Since \(15\cdot92<63\cdot22\), some hyperplane has at most 21 violations. Signed changes of coordinates take this hyperplane to the one labelled 36. Point rephasings fix the gauge on its frame. [Section reduction](lean/Quadric/Five/SectionChain.lean) · [Hyperplane count](lean/Quadric/Five/Hyperplanes.lean) · [Hyperplane coordinates](lean/Quadric/Five/LevelOneGeometry.lean)

There are 25 free bits in the normalized hyperplane. Its low-score list leads to 18 representative restrictions. Fixing the remaining gauge at label 4 leaves 31 free bits for each restriction. Split these bits into blocks of lengths 11, 10, and 10, with values \(h,a,b\). Every remaining line contains two outside labels, so its cost belongs to one of four sums,
\[
H(h)+A(h,a)+B(h,b)+C(a,b).
\]
For fixed \(h,a\), lower bounds for \(\min_b B(h,b)\) and \(\min_b C(a,b)\) exclude an entire row whenever their sum with \(H+A\) exceeds the cutoff. Every other row receives a full comparison over the 1,024 values of \(b\). The checker packs simultaneous costs into base-1,024 digits. Bounds on the cost and the comparison offset give a separate threshold bit for every digit. A matching bit mask proves both inclusion directions for each submitted row. [Digit arithmetic](lean/Quadric/Five/Packing.lean) · [Screening lemma](lean/Quadric/Five/OneBlock.lean) · [Connection to Pauli lines](lean/Quadric/Five/BlockGeometry.lean)

For a certificate signature, the 56 outside points carry independent signs. Their pair interactions correspond to 756 signed edges. Each triangle multiplier gives a valid inequality for its three signs. An integer factor and a residual matrix satisfy \(sM=LL^{\mathsf T}+R\), with positive integer scale \(s\). Each diagonal residual exceeds twice the sum of the absolute upper-triangular off-diagonal residuals. Bounding the cross terms shows that the original certificate quadratic form is nonnegative on integer vectors, including every outside sign vector. The certificate's rational bound then gives at least 315 violations after adding the section score. Signed transporter words carry the census results to these 42 signatures while preserving the numbers of violated lines. [Certificate arithmetic](lean/Quadric/Five/Certificates.lean) · [Quadratic form](lean/Quadric/Five/Gram.lean) · [Signed line transport](lean/Quadric/Five/Moves.lean)

The unconditional Lean endpoint is `Quadric.Five.degree_five`. It applies the signed census classification to every low-error restriction, transfers the resulting integer bound through both section covers, and uses the mixed-point witness for equality. [Theorem](lean/Quadric/Five/Exact.lean) · [Kernel replay](logs/claim-c-final-replay.txt)
