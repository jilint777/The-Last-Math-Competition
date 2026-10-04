# Counterexample to conjecture 00000009614

The conjecture says that the dimension groups of two mixing SFTs are order-isomorphic
**if and only if** the Perron eigenvalues λ_A and λ_B generate the same real number field
with agreeing unit group cosets. The **"if" direction is false**, so the biconditional
is false too.

| | matrix | mixing | Perron eigenvalue | spectrum | dimension group | rank |
|---|---|---|---|---|---|---|
| A | `[4]` (full 4-shift) | positive | 4, eigenvector (1) | {4} | Z[1/4] | 1 |
| B | `[[3,1],[1,3]]` | positive | 4, eigenvector (1,1) | {4, 2} | contains Z², inside Q² | 2 |

- **The right-hand side holds under every reading.** λ_A = λ_B = 4, so:
  - both generate the field Q;
  - their unit cosets agree in any sense (for example λ_A·{±1} = λ_B·{±1});
  - the entropies are both log 4;
  - even the Perron-eigenvector ideal classes agree (both trivial).

  Any condition on the pair (λ_A, λ_B) that holds for equal numbers is satisfied.
- **The dimension groups differ.** In Δ_A = lim(Z, ·4), any two elements p, q satisfy a
  nontrivial integer relation a·p + b·q = 0. In Δ_B = lim(Z², B), the classes of e₁ and
  e₂ are independent, because B is injective (det B = 8) and so B^t (a,b) = 0 forces
  a = b = 0.

  So there is no injective homomorphism Δ_B → Δ_A. The two groups are not isomorphic as
  abstract groups, so they are not order-isomorphic either, and their dimension triples
  are not isomorphic.
- **Second obstruction (triple reading).** By Krieger's theorem, an isomorphism of
  dimension triples means A and B are shift equivalent. Shift-equivalent matrices have the
  same nonzero spectrum, but here they are {4} and {4, 2}; equivalently tr Aᵏ = 4ᵏ ≠ 4ᵏ + 2ᵏ = tr Bᵏ.

## The irreducible variant also fails (report §6)

Take A' = [[4,1],[15,4]] and B' = [[4,3],[5,4]].

- **Setup.** Both matrices are positive. Both have the same irreducible characteristic
  polynomial t² − 8t + 1, so λ = 4 + √15 (a unit) and the zeta functions are equal.
- **The groups.** Since det = 1, Δ = Z² for both. The positive cone is
  {x : x·r > 0} ∪ {0}, where r is the right Perron eigenvector: (1, √15) for A' and
  (3, √15) for B'.
- **No order isomorphism.** An order isomorphism x ↦ xg (g ∈ GL₂(Z)) would need
  g r_B ∈ R₊ r_A. That forces g = [[a,b],[5b,3a]] with det g = 3a² − 5b² ≡ 3a² (mod 5),
  which lies in {0, 2, 3} mod 5, so det g ≠ ±1.
- **Ideal-class view.** The ideal ⟨3, √15⟩ of Z[√15] is not principal, because
  x² − 15y² = ±3 has no solution mod 5. Equivalently, the continued-fraction periods
  (1,6) and (2,3) differ.
- **Conventions.** The column convention leads to the same argument after a coordinate
  swap.

**Where each part is checked:**
- **Lean (arithmetic core only):** primitivity (`primitive_A2`, `primitive_B2`), the
  trace and determinant (`charpoly_A2_B2`), and `no_GL2_transport`, which says
  15b = 3c ∧ 3a = d ⇒ det ≠ ±1.
- **Report and `verify.py` only:**
  - the description of the cone;
  - the reduction of an order isomorphism to g r_B ∈ R₊ r_A;
  - the brute force over all 744 matrices g ∈ GL₂(Z) with entries |·| ≤ 6;
  - the continued fractions.

The report also includes two remarks:
- the "only if" direction is doubtful under the literal coset reading:
  Δ_[2] = Z[1/2] = Δ_[4] as ordered groups, but 2·{±1} ≠ 4·{±1};
- the side remark "the ordered isomorphism type is a flow invariant" is neither used nor
  endorsed.

## Contents

- `report.tex`, `report.pdf`: the complete proof, including the discussion of readings
  and models (direct limit vs eventual range, row vs column).
- `lean4/`: a self-contained Lean 4.19.0 project (core library only, no Mathlib).
- `verify.py` (Python 3 standard library) is an independent check in exact rational
  arithmetic. It covers:
  - characteristic polynomials and spectral radius;
  - path counts;
  - rank 1 and rank 2 in the eventual-range model;
  - brute force over identifications in the direct limit;
  - trace and spectrum invariants;
  - the irreducible variant (cones, GL₂(Z) brute force, mod-5 argument, continued fractions).
- `verification.txt`: the fresh build log, forbidden-token scan and `verify.py` output.

## Lean (`lean4/Main.lean`, namespace `DimGroup`)

- **Dimension group.** For any n × n integer matrix `M`, `DG M` is the dimension group,
  defined as the quotient of `Vec n × Nat` by `(v,k) ~ (w,l) ⇔ ∃ t, v M^(l+t) = w M^(k+t)`.
  - Addition, negation and zero are defined on the quotient, and their well-definedness
    is proved.
  - `add_comm'`, `add_assoc'`, `zero_add'` and `neg_add'` prove the abelian group axioms.
  - `Pos M` is the positive cone.
- **Isomorphisms.** `GroupIso` is an additive bijection. `OrderIso` additionally
  preserves `Pos` in both directions. `OrderIso.refl` shows these notions are not vacuous.
- **Rank.**
  - `rank_one`: every 1 × 1 dimension group has rank 1.
  - `rank_two`: `[e₁]` and `[e₂]` are independent in `Δ_B`.
  - `no_injective_hom`, `not_groupIso_AB` and `not_orderIso_AB` combine these.
- **Hypotheses of the conjecture.** `Primitive` means nonnegative with a positive power.
  `IsPerronEig M λ` means `λ` has a positive left eigenvector.
  - These are proved for `A` and `B` with λ = 4.
  - `second_eig_B` exhibits the eigenvalue 2, so spec B = {4, 2}.
  - `pathCount_A` and `pathCount_B` give the path counts 4ᵏ and 2·4ᵏ (equal entropy).
- **Main theorems.**
  - `conjecture_00000009614_false (Cond) (hrefl : ∀ x, Cond x x) : ¬ IfDirection Cond`.
    Here `IfDirection Cond` says: for all primitive integer matrices A, B with integer
    Perron eigenvalues satisfying `Cond λ_A λ_B`, the dimension groups are
    order-isomorphic. `Cond` is an arbitrary reflexive reading of "same field with
    agreeing unit cosets".
  - `conjecture_00000009614_iff_false` refutes the biconditional.
  - `conjecture_00000009614_group_false` refutes even the version with group isomorphism.
  - `conjecture_00000009614_false_Q` handles the concrete reading λ_A = ±λ_B (field Q,
    units ±1).
  - `nonvacuous` records that all the hypotheses are satisfiable.
- **Irreducible variant.** `primitive_A2`, `primitive_B2`, `charpoly_A2_B2` and
  `no_GL2_transport` (the arithmetic core only; see above).

The project has no `sorry`, no `native_decide` and no added axioms. `#print axioms` shows
only `propext` and `Quot.sound`.

**Not formalized:**
- the Perron–Frobenius theorem itself, that a positive eigenvector characterizes the
  spectral radius (for B, Lean exhibits both eigenvalues);
- the isomorphism between the direct-limit model and the eventual-range model (the report
  gives the rank argument in both models);
- Krieger's theorem, which is used only for the redundant second obstruction;
- for the irreducible variant: the description of the cone and the reduction of an order
  isomorphism to g r_B ∈ R₊ r_A.

## Reproduce

```sh
cd lean4 && lake build
cd .. && python3 verify.py
pdflatex report.tex && pdflatex report.tex
```

## 中文说明

猜想断言：两个混合有限型子移位（SFT）的维数群有序同构，当且仅当它们的 Perron 特征值
λ_A 与 λ_B 生成相同的实代数数域，并且单位群陪集一致。我们否定其中“当”（充分性）这一方向，
因此整个“当且仅当”命题不成立。

**反例。** A = [4]（全 4-移位），B = [[3,1],[1,3]]。

- 两者都是正矩阵，所以是本原矩阵，对应的 SFT 是混合的。
- 两者的 Perron 特征值都是 4，正特征向量分别为 (1) 与 (1,1)；熵都是 log 4。
- 因为 λ_A = λ_B，所以无论怎样理解“生成相同数域且单位群陪集一致”，条件都成立。
  甚至 Perron 特征向量的理想类也一致（都平凡）。

**维数群不同构。**

- Δ_A ≅ Z[1/4] 的秩为 1：任意两个元素都满足非平凡的整系数线性关系。
- B 可逆（det B = 8），所以 e₁、e₂ 在 Δ_B 中线性无关，Δ_B 的秩为 2。

因此不存在从 Δ_B 到 Δ_A 的单射同态。两者作为抽象群都不同构，更谈不上有序同构，
维数三元组也不同构。

另一个独立的障碍：由 Krieger 定理，维数三元组同构等价于移位等价；而移位等价的矩阵有相同的非零谱，
这里两者的非零谱分别是 {4} 和 {4,2}，不相同。

**不可约特征多项式的情形同样不成立（报告第 6 节）。**

取 A' = [[4,1],[15,4]] 与 B' = [[4,3],[5,4]]。

- 两者都是正矩阵，特征多项式都是不可约的 t² − 8t + 1，因此 λ = 4 + √15，zeta 函数也相同。
- det = 1，所以两者的维数群都是 Z²；正锥为 {x : x·r > 0} ∪ {0}，其中 r 为右 Perron 特征向量，
  分别是 (1, √15) 与 (3, √15)。
- 有序同构必须满足 g r_B ∈ R₊ r_A，由此 g = [[a,b],[5b,3a]]，det g = 3a² − 5b²；
  模 5 它只能是 0、2、3，不可能等于 ±1。
- 等价地说，Z[√15] 的理想 ⟨3, √15⟩ 不是主理想。

其中，算术核心（no_GL2_transport）、本原性以及迹与行列式已在 Lean 中证明；
正锥刻画与“有序同构 ⇒ g r_B ∈ R₊ r_A”这一约化只在报告和 verify.py 中给出
（verify.py 还对 744 个元素绝对值不超过 6 的 GL₂(Z) 矩阵做了穷举检验）。

另外两点说明：

- 在字面的陪集解释下，“仅当”方向也可疑：Δ_[2] = Z[1/2] = Δ_[4]，但 2·{±1} ≠ 4·{±1}。
- 我们既不使用也不认可“有序同构型是流不变量”这一旁注。

**Lean 形式化（仅用 Lean 4.19.0 核心库）。**

- 对一般整数矩阵，把维数群定义为正向极限的商类型，并证明它是交换群；同时定义了正锥、群同构与有序同构。
- 证明了秩 1 与秩 2 的论断，以及本原性、Perron 特征值和路径计数。
- 主定理 `conjecture_00000009614_false`：对任意自反的条件 Cond，“充分性”方向为假。

`verify.py` 用精确有理数运算独立验证上述全部事实。
