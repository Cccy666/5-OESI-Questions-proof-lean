# A219692：有限和桥接与递推

最终 Lean 定理见 `Main.lean`。原序列第零项为2，原递推适用于 n≥3；归一化序列第零项为1，其递推适用于 n≥2。

## 0. 定义与范围

令 \(b_m=\binom{2m}{m}\)，其中 \(m\ge0\)。对 \(n\ge0\) 定义

\[
C_n(A,B)=\sum_{j=0}^n\binom nj b_jb_{n-j}A^{n-j}B^j
\quad\in\mathbb Z[A,B].
\]

原序列第零项**单独定义**为 \(a_0=2\)。对 \(n\ge1\) 定义

\[
a_n=\sum_{j=0}^{\lfloor n/3\rfloor}
(-1)^j\binom nj b_jb_{n-j}
\left(\binom{2n-3j-1}{n}+\binom{2n-3j}{n}\right).
\]

正项序列在全部 \(n\ge0\) 上定义为

\[
v_n=\sum_{j=0}^{\lfloor n/3\rfloor}
3^{n-3j}b_{n-j}\binom{n-j}{2j}b_j^2.
\]

本文证明 \(a_n=v_n\) 对所有 \(n\ge1\) 成立，而 \(a_0=2\ne1=v_0\)。
全部出现的普通二项式上指标非负；下指标超出 \([0,N]\) 时约定 \(\binom Nr=0\)。
普通多项式和形式幂级数的负次数系数取零。

## 1. P1：三项式系数证明

对整数 \(0\le2k\le n\)，有

\[
\sum_{\ell=k}^{\lfloor n/2\rfloor}
\binom n{2\ell}\binom{2\ell}{\ell}\binom\ell k2^{n-2\ell}
=\binom nk\binom{2n-2k}{n}.
\tag{P1}
\]

记 \(m=n-2k\ge0\)，\(N=n-k=m+k\)。由
\((1+z)^{2N}=(1+2z+z^2)^N\) 比较 \(z^m\) 系数，得

\[
\binom{2N}{m}
=\sum_{r=0}^{\lfloor m/2\rfloor}
\frac{N!}{r!\,(m-2r)!\,(k+r)!}\,2^{m-2r}.
\tag{1}
\]

因为在三项式展开中，分别选取 \(r\) 个 \(z^2\)、\(m-2r\) 个
\(2z\)、\(k+r\) 个 \(1\)。这些计数均非负且总和为 \(N\)，
每个产生 \(z^m\) 的选取唯一具有这种形式。

将 (1) 乘以 \(\binom nk=n!/(k!N!)\)，再令 \(\ell=k+r\)。右侧单项变为

\[
\frac{n!\,2^{n-2\ell}}{k!\,(\ell-k)!\,(n-2\ell)!\,\ell!}
=\binom n{2\ell}\binom{2\ell}{\ell}\binom\ell k2^{n-2\ell}.
\]

左侧是 \(\binom nk\binom{2N}{m}=\binom nk\binom{2n-2k}{n}\)，
因为 \(2N-m=n\)。这就证明 P1，包括 \(n=k=0\)。

后续还使用等价阶乘恒等式

\[
\binom nk\binom{2n-2k}{n}
=b_{n-k}\binom{n-k}{k}.
\tag{2}
\]

两边均为 \((2n-2k)!/[k!(n-k)!(n-2k)!]\)，所有阶乘指标非负。

## 2. P：有限 Laurent 多项式常数项证明

对任意 \(n\ge0\)，在 \(\mathbb Z[A,B]\) 中有

\[
C_n(A,B)=\sum_{k=0}^{\lfloor n/2\rfloor}
(-1)^kb_kb_{n-k}\binom{n-k}{k}(AB)^k(A+B)^{n-2k}.
\tag{P}
\]

以下所有常数项运算都在**有限** Laurent 多项式环中进行，因此没有
收敛、无限求和换序或形式展开方向问题。先有

\[
\operatorname{CT}_x(2+x+x^{-1})^m=b_m,
\tag{3}
\]

因为 \((2+x+x^{-1})^m=x^{-m}(1+x)^{2m}\)。于是

\[
C_n(A,B)=\operatorname{CT}_{x,y}
\bigl(A(2+x+x^{-1})+B(2+y+y^{-1})\bigr)^n.
\tag{4}
\]

代入 \(x=pq,\ y=p/q\)。Laurent 单项式 \(x^ry^s\) 变成
\(p^{r+s}q^{r-s}\)。其指数同时为零当且仅当 \(r=s=0\)，
因为 \(r+s=0=r-s\) 推出 \(2r=2s=0\)（指数为整数）。
因此这个代入保持常数项；这里只需指数映射的单射性，无需满射性。

设 \(s_0=A+B\)。式 (4) 变成

\[
\operatorname{CT}_{p,q}
\left(2s_0+p(Aq+Bq^{-1})+p^{-1}(Aq^{-1}+Bq)\right)^n.
\]

先提取 \(p\) 的常数项。若选取 \(\ell\) 个含 \(p\) 的项，
必须也选取 \(\ell\) 个含 \(p^{-1}\) 的项，故上式等于

\[
\sum_{\ell=0}^{\lfloor n/2\rfloor}
\binom n{2\ell}b_\ell(2s_0)^{n-2\ell}
\operatorname{CT}_q
\left((Aq+Bq^{-1})(Aq^{-1}+Bq)\right)^\ell.
\tag{5}
\]

用纯多项式恒等式

\[
(Aq+Bq^{-1})(Aq^{-1}+Bq)
=s_0^2+AB(q-q^{-1})^2
\]

以及

\[
\operatorname{CT}_q(q-q^{-1})^{2k}=(-1)^k\binom{2k}{k}=(-1)^kb_k
\]

展开 (5)，再对有限三角索引集 \(0\le k\le\ell\le\lfloor n/2\rfloor\)
交换求和顺序，得到

\[
C_n(A,B)=\sum_{k=0}^{\lfloor n/2\rfloor}
(-1)^kb_k(AB)^ks_0^{n-2k}
\sum_{\ell=k}^{\lfloor n/2\rfloor}
\binom n{2\ell}b_\ell\binom\ell k2^{n-2\ell}.
\]

应用 P1 和 (2) 即得 P。证明中没有除以 \(A\)、\(B\) 或 \(A+B\)，
故它们取零或 \(A+B=0\) 时无需另作例外。常数多项式的零次幂为 1。

## 3. C：单项式与形式导数证明

对 \(n\ge0\) 和 \(Q\in\mathbb Q[w]\)，有

\[
[t^n](1+2t)(1+t)^{-n-1}Q(t(1+t))=[w^n]Q(w).
\tag{C}
\]

这里 \((1+t)^{-1}\in\mathbb Q[[t]]\) 是常数项为 1 的单位 \(1+t\)
的形式乘法逆元。所有负整数次幂均属于 \(\mathbb Q[[t]]\)，
没有负次数项。由对多项式 \(Q\) 的线性性，只需证明 \(Q(w)=w^m\)
的情形，其中 \(m\ge0\)。左侧为

\[
[t^{n-m}](1+2t)(1+t)^{m-n-1}.
\tag{6}
\]

* 若 \(m>n\)，因为原式含因子 \(t^m\)，(6) 为零。
* 若 \(m=n\)，(6) 为常数项 1。
* 若 \(m<n\)，令 \(r=n-m\ge1\)，\(f=(1+t)^{-r}\)。利用
  \(1+2t=(1+t)+t\)，(6) 等于

  \[
  [t^r]f+[t^{r-1}](1+t)^{-r-1}.
  \]

  形式导数乘积法则给出 \(f'=-r(1+t)^{-r-1}\)，而导数系数定义给出
  \([t^{r-1}]f'=r[t^r]f\)。由于 \(r\ne0\) 在 \(\mathbb Q\) 中可逆，
  \([t^{r-1}](1+t)^{-r-1}=-[t^r]f\)，故 (6) 为零。

于是 (6) 恰为 Kronecker delta \(\delta_{mn}\)，证明 C。
这里只有有限多个 \(m\)，没有无限求和换序。此证明也解释为什么使用
\(\mathbb Q[[t]]\)，而不贸然声称同一导数论证适用于任意正特征环。

## 4. B1：原和式的系数表示

对 \(n\ge1\)，有

\[
a_n=[t^n](1+2t)(1+t)^{-n-1}C_n((1+t)^3,-t^3).
\tag{B1}
\]

展开 \(C_n\)，右侧是

\[
\sum_{j=0}^n(-1)^j\binom njb_jb_{n-j}
[t^n]t^{3j}(1+2t)(1+t)^{2n-3j-1}.
\tag{7}
\]

所有整数指数幂 \((1+t)^{2n-3j-1}\)，即使指数为负，也属于
\(\mathbb Q[[t]]\)。因此 \(3j>n\) 时相应项的最低可能次数为 \(3j>n\)，
对 (7) 无贡献。可将范围缩为 \(0\le j\le\lfloor n/3\rfloor\)。

在该范围内设 \(r=n-3j\ge0\)，\(M=2n-3j=n+r\ge n\ge1\)，
则 \(M-1\ge0\)，所需系数为

\[
\begin{aligned}
[t^r](1+2t)(1+t)^{M-1}
&=[t^r](1+t)^M+[t^{r-1}](1+t)^{M-1}\\
&=\binom Mr+\binom{M-1}{r-1}\\
&=\binom Mn+\binom{M-1}n.
\end{aligned}
\tag{8}
\]

最后一行在 \(r\ge1\) 时直接使用二项式对称性；在 \(r=0\) 时，
第二项是负次数系数零，且 \(M=n\) 导致 \(\binom{M-1}n=0\)，
所以等式仍成立。将 (8) 放回 (7) 恰为 \(a_n\) 的定义。

**第零项审计。** \(n=0\) 时 B1 右侧为
\([t^0](1+2t)/(1+t)=1\)。原序列按定义 \(a_0=2\)，因此 B1
不能延伸到 \(n=0\)。上述证明精确使用 \(M\ge1\) 以保证 \(M-1\)
非负；若 \(n=j=0\)，不能把普通非负上指标的二项式对称性套到 \(-1\)。

## 5. Bridge：合成与最后的支持集检查

固定 \(n\ge1\)，并定义真正的多项式

\[
Q_n(w)=\sum_{k=0}^{\lfloor n/2\rfloor}
b_kb_{n-k}\binom{n-k}{k}w^{3k}(1+3w)^{n-2k}\in\mathbb Z[w].
\]

将 \(A=(1+t)^3\)、\(B=-t^3\) 代入 P，并令 \(w=t(1+t)\)。
由于 \(A+B=1+3w\)、\(AB=-w^3\)，有

\[
C_n((1+t)^3,-t^3)=Q_n(t(1+t)).
\]

B1 与 C 给出 \(a_n=[w^n]Q_n(w)\)。在 \(Q_n\) 中，\(3k>n\)
的单项最低次数大于 \(n\)，故恰可将系数求和缩为
\(0\le k\le\lfloor n/3\rfloor\)。每个留下的项满足 \(n-2k\ge n-3k\ge0\)，
因此普通二项式定理给出

\[
a_n=\sum_{k=0}^{\lfloor n/3\rfloor}
3^{n-3k}b_kb_{n-k}\binom{n-k}{k}\binom{n-2k}{n-3k}.
\]

在此支持集上，全部阶乘指标非负，且

\[
\binom{n-k}{k}\binom{n-2k}{n-3k}
=\frac{(n-k)!}{k!^2(n-3k)!}
=\binom{n-k}{2k}\binom{2k}{k}.
\]

故

\[
\boxed{a_n=v_n\quad(n\ge1).}
\tag{Bridge}
\]

独立计算 \(v_0=b_0\binom00b_0^2=1\)。因此若定义
\(u_0=1\)、\(u_n=a_n\ (n\ge1)\)，则 \(u_n=v_n\) 对全部 \(n\ge0\) 成立。
这最后一步依赖显式分段定义，没有把原序列第零项悄悄替换。

# 递推证明

## 1. 精确定义

对自然数 n,j 定义

\[
S(n,j)=\begin{cases}
3^{n-3j}\binom{2n-2j}{n-j}\binom{n-j}{2j}\binom{2j}{j}^2,&3j\le n,\\
0,&3j>n.
\end{cases}
\]

令 \(v_n=\sum_{j=0}^{\lfloor n/3\rfloor}S(n,j)\)，并令

\[
p_n=2(2n-1)(7n^2-7n+3),\qquad
q_n=12(4n-5)(n-1)(4n-3).
\]

所有减法及系数运算都在整数/有理数中进行，只有合法支持集上的
阶乘、二项式下标和幂指数使用非负整数。
对 n≥2 定义

\[
G(n,j)=-\frac{9(4n-3)j^3}{2n-2j-1}S(n,j)\in\mathbb Q.
\]

分母是奇整数，故对每个整数 n,j 均不为零。支持集外 S=0 使 G=0，
没有对 S 作除法。

## 2. 支持集和平移等式

固定 n≥2,j≥0，记
\(t=n-3j\)、\(d=2n-2j-1\)、\(e=2n-2j-3=d-2\)。
三条交叉相乘等式为

\[
6dS(n-1,j)=tS(n,j), \tag{Sh1}
\]
\[
36deS(n-2,j)=t(t-1)S(n,j), \tag{Sh2}
\]
\[
27(j+1)^3dS(n,j+1)
=(2j+1)t(t-1)(t-2)S(n,j). \tag{ShJ}
\]

### 2.1 合法阶乘区间内的推导

在支持集内由二项式定义精确化简得到

\[
S(n,j)=3^{n-3j}\frac{(2n-2j)!(2j)!}
{(n-j)!j!^4(n-3j)!}. \tag{SF}
\]

这个 SF 与初始地图错误的原交错单项 T 是不同公式。

若 t≥1，两边都在支持集内。令 m=n−j，则

\[
\frac{S(n-1,j)}{S(n,j)}
=\frac{1}{3}\frac{m\,t}{(2m)(2m-1)}
=\frac{t}{6d}.
\]

这里 m>0，S(n,j)>0，合法约分得到 Sh1。
这个比值推导本身只需要其基指标至少为 1 且 t≥1，
故也覆盖第二次平移可能出现的基指标 1（此时只能 j=0）。
若 t≥2，连续使用这条合法比值给出
\(S(n-2,j)/S(n,j)=t(t-1)/(36de)\)，即 Sh2。

若 t≥3，SF 给出

\[
\frac{S(n,j+1)}{S(n,j)}
=\frac{(2j+2)(2j+1)m\,t(t-1)(t-2)}
{27(2m)(2m-1)(j+1)^4}
=\frac{(2j+1)t(t-1)(t-2)}{27(j+1)^3d},
\]

得到 ShJ。以上阶乘指标均非负。

### 2.2 全部边界的补足

若 t<0，即 3j>n，S(n,j)、S(n−1,j)、S(n−2,j)、S(n,j+1)
全部为零，三条交叉等式两边均零。

若 t=0，S(n−1,j)=S(n−2,j)=S(n,j+1)=0；三条右侧均有因子 t。
若 t=1，Sh1 已在合法区间证明；S(n−2,j)=S(n,j+1)=0，
Sh2/ShJ 的右侧均有因子 t−1。
若 t=2，Sh1/Sh2 已证明；S(n,j+1)=0，ShJ 的右侧有因子 t−2。
这些分支覆盖全部整数 t，因此没有把泛型有理比值用在零项上。

在支持集 t≥0 下，n≥2 还蕴含 n−j≥2，因此 d≥3、e≥1。
在支持集外 d,e 仍为非零奇数。

## 3. 无分母多项式证书与 Tel

下式是 \(\mathbb Z[n,j]\) 中的多项式恒等式：

\[
\begin{aligned}
36den^3-6e p_nt+q_nt(t-1)
={}&-12(4n-3)(2j+1)t(t-1)(t-2)\\
&+324(4n-3)j^3e.
\end{aligned} \tag{PC}
\]

PC 可直接展开两边证明。可复现核验有三条独立路径：
继承脚本的 SymPy 有理函数化简、本项目标准库稀疏整数多项式乘法、
以及 `Certificates.lean` 的环恒等式证明（具体已编译范围见 formal 记录）。
标准库展开两边各有 13 个非零单项式，差为零。

把 PC 乘以 S(n,j)，再使用 Sh1/Sh2/ShJ。
由于 d,e,j+1 均不为零，ShJ 给出

\[
36deG(n,j+1)
=-12(4n-3)(2j+1)t(t-1)(t-2)S(n,j).
\]

G 的定义直接给出
\(36deG(n,j)=-324(4n-3)j^3eS(n,j)\)。
PC 左侧相应变成
\(36de(n^3S(n,j)-p_nS(n-1,j)+q_nS(n-2,j))\)。
除以非零的 36de，即得全域局部等式

\[
\boxed{n^3S(n,j)-p_nS(n-1,j)+q_nS(n-2,j)
=G(n,j+1)-G(n,j)} \tag{Tel}
\]

对每个 n≥2,j≥0 成立。也可以将 j 在支持集外的情形单独写为 0=0，
避免在该分支使用任何分式化简。

## 4. GZ 的整数表达与端点

若 1≤j 且 3j≤n，令 m=n−j≥2j≥2。合法阶乘恒等式为

\[
\frac{\binom{2m-2}{m-1}}{\binom{2m}{m}}
=\frac{m}{2(2m-1)},\qquad
\frac{\binom{m-1}{2j-1}}{\binom m{2j}}=\frac{2j}{m}.
\]

它们的乘积为 j/(2m−1)。代回 G 得到

\[
G(n,j)=-9(4n-3)3^{n-3j}j^2
\binom{2n-2j-2}{n-j-1}
\binom{n-j-1}{2j-1}\binom{2j}{j}^2. \tag{GZ}
\]

在 j=0 或 3j>n 时，G=0；GZ 的分段版本同样定义为零。
因此 G 的值实际为整数，但前面的有理数证明无需此整数性。

若 N=⌊n/3⌋，则 3(N+1)>n，所以
\(G(n,0)=G(n,N+1)=0\)。第一个等式来自 j³=0，第二个来自支持集。

## 5. 有限求和与 T1/T2/T0

在统一范围 0≤j≤N 上求和 Tel。对于 r=0,1,2，
n−r≥0 且 ⌊(n−r)/3⌋≤N；因此零延拓保证

\[
\sum_{j=0}^{N}S(n-r,j)=v_{n-r}.
\]

望远镜和严格等于 G(n,N+1)−G(n,0)=0，所以

\[
\boxed{n^3v_n-p_nv_{n-1}+q_nv_{n-2}=0\quad(n\ge2).} \tag{VRec}
\]

初值直接由有限和得 v₀=1,v₁=6。`bridge_proof.md` 独立于递推证明
aₙ=vₙ 对 n≥1 成立。故显式归一化 u₀=1,uₙ=aₙ(n≥1) 满足 u=v，得到

\[
\boxed{n^3u_n-p_nu_{n-1}+q_nu_{n-2}=0\quad(n\ge2).} \tag{T1}
\]

若 n≥3，则 n,n−1,n−2 均至少为 1，可逐项替换，得到

\[
\boxed{n^3a_n-p_na_{n-1}+q_na_{n-2}=0\quad(n\ge3).} \tag{T2}
\]

原初值为 a₀=2,a₁=6,a₂=54，p₂=102,q₂=180。因此

\[
\boxed{8\cdot54-102\cdot6+180\cdot2=180\ne0.} \tag{T0}
\]

原序列的 n≥2 版本被反驳；这与 T1/T2 是三个不同声明。
初始地图 A2 的算式误写 126；本项目第一版文字也误抄，后由 Lean 初值审计
纠正为102。符号定义、程序与 Lean 实际一直使用正确的 p₂=102。
