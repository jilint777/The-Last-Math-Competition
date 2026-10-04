/-!
# Conjecture 00000009614: equal Perron eigenvalues do not force isomorphic dimension groups

The conjecture states that the dimension groups of two mixing SFTs `X_A`, `X_B` are
order-isomorphic **if and only if** the Perron eigenvalues `λ_A`, `λ_B` generate the same
real number field with agreeing unit group cosets.  We refute the "if" direction.

* `A = [4]` (the full 4-shift) and `B = [[3,1],[1,3]]` are primitive (positive) matrices,
  so `X_A`, `X_B` are mixing SFTs.  Both have Perron eigenvalue `4` (positive eigenvectors
  `(1)` and `(1,1)`).  Hence `λ_A = λ_B`, and every condition on the pair `(λ_A, λ_B)` that
  holds for equal arguments (same field `ℚ(λ)`, same unit coset `λ·U`, ...) is satisfied.
* The dimension group `Δ_M` of an `n × n` integer matrix `M` is the direct limit
  `ℤⁿ →M ℤⁿ →M ⋯` (Krieger; Lind–Marcus §7.5): pairs `(v, k)` with `v ∈ ℤⁿ`, `k ∈ ℕ`,
  where `(v, k) ~ (w, l)` iff `v M^(l+t) = w M^(k+t)` for some `t`.  Its positive cone is
  the set of classes of `(v, k)` with `v M^t ≥ 0` for some `t`.
* Any two elements of `Δ_A` are `ℤ`-linearly dependent (rank 1), while the classes of
  `e₁`, `e₂` in `Δ_B` are `ℤ`-linearly independent (rank 2).  Hence there is no injective
  additive map `Δ_B → Δ_A`; in particular `Δ_A`, `Δ_B` are not isomorphic as groups, let
  alone as ordered groups.

Vectors are `Fin n → Int` (row vectors) and matrices are `Fin n → Fin n → Int`.
-/

namespace DimGroup

/-! ## Vectors, matrices, row-vector multiplication -/

abbrev Vec (n : Nat) := Fin n → Int
abbrev Mat (n : Nat) := Fin n → Fin n → Int

/-- `fsum n f = f 0 + ⋯ + f (n-1)`. -/
def fsum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + fsum n (fun i => f i.succ)

theorem fsum_add (n : Nat) (f g : Fin n → Int) :
    fsum n (fun i => f i + g i) = fsum n f + fsum n g := by
  induction n with
  | zero => simp [fsum]
  | succ n ih =>
    simp only [fsum]
    rw [ih (fun i => f i.succ) (fun i => g i.succ)]
    omega

theorem fsum_neg (n : Nat) (f : Fin n → Int) :
    fsum n (fun i => - f i) = - fsum n f := by
  induction n with
  | zero => simp [fsum]
  | succ n ih =>
    simp only [fsum]
    rw [ih (fun i => f i.succ)]
    omega

theorem fsum_zero (n : Nat) : fsum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fsum]; rw [ih]; rfl

variable {n : Nat}

def vadd (u v : Vec n) : Vec n := fun i => u i + v i
theorem vadd_comm (u v : Vec n) : vadd u v = vadd v u := funext fun _ => Int.add_comm _ _
def vneg (u : Vec n) : Vec n := fun i => - u i
def vzero : Vec n := fun _ => 0
/-- `c • u`. -/
def vsmul (c : Int) (u : Vec n) : Vec n := fun i => c * u i
/-- The standard basis vector `e_i`. -/
def basis (i : Fin n) : Vec n := fun j => if i = j then 1 else 0

/-- Row vector times matrix: `(v M)_j = Σ_i v_i M_ij`. -/
def rmul (M : Mat n) (v : Vec n) : Vec n := fun j => fsum n (fun i => v i * M i j)

/-- `pw M t v = v M^t`. -/
def pw (M : Mat n) : Nat → Vec n → Vec n
  | 0, v => v
  | t + 1, v => rmul M (pw M t v)

theorem pw_add (M : Mat n) (s t : Nat) (v : Vec n) :
    pw M (s + t) v = pw M t (pw M s v) := by
  induction t with
  | zero => rfl
  | succ t ih => show rmul M (pw M (s + t) v) = rmul M (pw M t (pw M s v)); rw [ih]

theorem rmul_vadd (M : Mat n) (u v : Vec n) :
    rmul M (vadd u v) = vadd (rmul M u) (rmul M v) := by
  funext j
  simp only [rmul, vadd]
  rw [← fsum_add]
  congr 1
  funext i
  exact Int.add_mul _ _ _

theorem rmul_vneg (M : Mat n) (u : Vec n) : rmul M (vneg u) = vneg (rmul M u) := by
  funext j
  simp only [rmul, vneg]
  rw [← fsum_neg]
  congr 1
  funext i
  exact Int.neg_mul _ _

theorem rmul_vzero (M : Mat n) : rmul M vzero = vzero := by
  funext j
  simp only [rmul, vzero, Int.zero_mul]
  exact fsum_zero n

theorem pw_vadd (M : Mat n) (t : Nat) (u v : Vec n) :
    pw M t (vadd u v) = vadd (pw M t u) (pw M t v) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [pw]; rw [ih, rmul_vadd]

theorem pw_vneg (M : Mat n) (t : Nat) (u : Vec n) : pw M t (vneg u) = vneg (pw M t u) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [pw]; rw [ih, rmul_vneg]

theorem pw_vzero (M : Mat n) (t : Nat) : pw M t vzero = vzero := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [pw]; rw [ih, rmul_vzero]

/-! ## The dimension group as a direct limit -/

/-- `(v, k) ~ (w, l)` iff `v M^(l+t) = w M^(k+t)` for some `t`. -/
def Rel (M : Mat n) (p q : Vec n × Nat) : Prop :=
  ∃ t, pw M (q.2 + t) p.1 = pw M (p.2 + t) q.1

theorem Rel.refl (M : Mat n) (p : Vec n × Nat) : Rel M p p := ⟨0, rfl⟩

theorem Rel.symm {M : Mat n} {p q : Vec n × Nat} : Rel M p q → Rel M q p :=
  fun ⟨t, h⟩ => ⟨t, h.symm⟩

theorem Rel.trans {M : Mat n} {p q r : Vec n × Nat} :
    Rel M p q → Rel M q r → Rel M p r := by
  rintro ⟨t1, h1⟩ ⟨t2, h2⟩
  obtain ⟨u, k⟩ := p
  obtain ⟨v, l⟩ := q
  obtain ⟨w, m⟩ := r
  simp only at h1 h2 ⊢
  refine ⟨l + t1 + t2, ?_⟩
  rw [show m + (l + t1 + t2) = (l + t1) + (m + t2) by omega, pw_add, h1, ← pw_add,
    show k + t1 + (m + t2) = (m + t2) + (k + t1) by omega, pw_add, h2, ← pw_add,
    show l + t2 + (k + t1) = k + (l + t1 + t2) by omega]

instance dimSetoid (M : Mat n) : Setoid (Vec n × Nat) :=
  ⟨Rel M, ⟨Rel.refl M, Rel.symm, Rel.trans⟩⟩

/-- The dimension group `Δ_M = lim (ℤⁿ, M)`. -/
def DG (M : Mat n) : Type := Quotient (dimSetoid M)

/-- The class of `(v, k)`, i.e. "`v M^(-k)`". -/
def mk (M : Mat n) (v : Vec n) (k : Nat) : DG M := Quotient.mk (dimSetoid M) (v, k)

theorem mk_eq_iff (M : Mat n) (v w : Vec n) (k l : Nat) :
    mk M v k = mk M w l ↔ ∃ t, pw M (l + t) v = pw M (k + t) w :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Representative-level sum: `(u, k) + (v, l) = (u M^l + v M^k, k + l)`. -/
def addRep (M : Mat n) (p q : Vec n × Nat) : Vec n × Nat :=
  (vadd (pw M q.2 p.1) (pw M p.2 q.1), p.2 + q.2)

theorem addRep_comm (M : Mat n) (p q : Vec n × Nat) : Rel M (addRep M p q) (addRep M q p) := by
  refine ⟨0, ?_⟩
  obtain ⟨u, k⟩ := p
  obtain ⟨v, l⟩ := q
  show pw M ((l + k) + 0) (vadd (pw M l u) (pw M k v)) =
    pw M ((k + l) + 0) (vadd (pw M k v) (pw M l u))
  rw [Nat.add_comm l k, vadd_comm]

theorem addRep_left (M : Mat n) (p p' q : Vec n × Nat) (h : Rel M p p') :
    Rel M (addRep M p q) (addRep M p' q) := by
  obtain ⟨t, h⟩ := h
  obtain ⟨u, k⟩ := p
  obtain ⟨u', k'⟩ := p'
  obtain ⟨v, l⟩ := q
  simp only [addRep] at h ⊢
  refine ⟨t, ?_⟩
  rw [pw_vadd, pw_vadd, ← pw_add, ← pw_add, ← pw_add, ← pw_add]
  rw [show l + (k' + l + t) = (k' + t) + (l + l) by omega, pw_add, h, ← pw_add,
    show k + t + (l + l) = l + (k + l + t) by omega,
    show k + (k' + l + t) = k' + (k + l + t) by omega]

theorem addRep_right (M : Mat n) (p q q' : Vec n × Nat) (h : Rel M q q') :
    Rel M (addRep M p q) (addRep M p q') :=
  Rel.trans (addRep_comm M p q) (Rel.trans (addRep_left M q q' p h) (addRep_comm M q' p))

instance (M : Mat n) : Add (DG M) where
  add := Quotient.lift₂ (fun p q => Quotient.mk (dimSetoid M) (addRep M p q))
    (fun _ _ _ _ h1 h2 => Quotient.sound
      (Rel.trans (addRep_left M _ _ _ h1) (addRep_right M _ _ _ h2)))

instance (M : Mat n) : Neg (DG M) where
  neg := Quotient.lift (fun p => Quotient.mk (dimSetoid M) (vneg p.1, p.2))
    (fun p q ⟨t, h⟩ => Quotient.sound ⟨t, by
      show pw M (q.2 + t) (vneg p.1) = pw M (p.2 + t) (vneg q.1)
      rw [pw_vneg, pw_vneg, h]⟩)

instance (M : Mat n) : Zero (DG M) where
  zero := mk M vzero 0

theorem add_mk (M : Mat n) (u v : Vec n) (k l : Nat) :
    mk M u k + mk M v l = mk M (vadd (pw M l u) (pw M k v)) (k + l) := rfl

theorem neg_mk (M : Mat n) (u : Vec n) (k : Nat) : -(mk M u k) = mk M (vneg u) k := rfl

theorem zero_def (M : Mat n) : (0 : DG M) = mk M vzero 0 := rfl

/-- `(u, k) ~ (u M^s, k + s)`. -/
theorem mk_lift (M : Mat n) (u : Vec n) (k s K : Nat) (hK : K = k + s) :
    mk M u k = mk M (pw M s u) K := by
  subst hK
  refine Quotient.sound ⟨0, ?_⟩
  show pw M (k + s + 0) u = pw M (k + 0) (pw M s u)
  rw [show k + s + 0 = s + (k + 0) by omega, pw_add]

/-- At a common level, addition is vector addition. -/
theorem add_same (M : Mat n) (u v : Vec n) (k : Nat) :
    mk M u k + mk M v k = mk M (vadd u v) k := by
  rw [add_mk]
  refine Quotient.sound ⟨0, ?_⟩
  show pw M (k + 0) (vadd (pw M k u) (pw M k v)) = pw M (k + k + 0) (vadd u v)
  rw [pw_vadd, pw_vadd, ← pw_add, ← pw_add, show k + (k + 0) = k + k + 0 by omega]

theorem ind {M : Mat n} {P : DG M → Prop} (h : ∀ v k, P (mk M v k)) : ∀ x, P x :=
  Quotient.ind (fun p => h p.1 p.2)

/-! ### `Δ_M` is an abelian group -/

theorem add_comm' (M : Mat n) (x y : DG M) : x + y = y + x := by
  induction x using ind
  induction y using ind
  exact Quotient.sound (addRep_comm M _ _)

theorem add_assoc' (M : Mat n) (x y z : DG M) : x + y + z = x + (y + z) := by
  induction x using ind with | h u k =>
  induction y using ind with | h v l =>
  induction z using ind with | h w m =>
  rw [mk_lift M u k (l + m) (k + l + m) (by omega), mk_lift M v l (k + m) (k + l + m) (by omega),
    mk_lift M w m (k + l) (k + l + m) (by omega), add_same, add_same, add_same, add_same]
  congr 1
  funext i
  simp only [vadd]
  omega

theorem zero_add' (M : Mat n) (x : DG M) : 0 + x = x := by
  induction x using ind with | h u k =>
  rw [zero_def, mk_lift M vzero 0 k k (by omega), pw_vzero, add_same]
  congr 1
  funext i
  simp only [vadd, vzero]
  omega

theorem neg_add' (M : Mat n) (x : DG M) : -x + x = 0 := by
  induction x using ind with | h u k =>
  rw [neg_mk, add_same, zero_def, mk_lift M vzero 0 k k (by omega), pw_vzero]
  congr 1
  funext i
  simp only [vadd, vneg, vzero]
  omega

/-! ### Positive cone, isomorphisms -/

/-- The positive cone `Δ_M^+`: classes of `(v, k)` with `v M^t ≥ 0` for some `t`. -/
def Pos (M : Mat n) (x : DG M) : Prop :=
  ∃ v k t, x = mk M v k ∧ ∀ i, 0 ≤ pw M t v i

/-- A group isomorphism `Δ_M ≅ Δ_N`: an additive bijection. -/
structure GroupIso {m : Nat} (M : Mat n) (N : Mat m) where
  toFun : DG M → DG N
  invFun : DG N → DG M
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y

/-- An ordered-group isomorphism `(Δ_M, Δ_M^+) ≅ (Δ_N, Δ_N^+)`. -/
structure OrderIso {m : Nat} (M : Mat n) (N : Mat m) extends GroupIso M N where
  map_pos : ∀ x, Pos M x ↔ Pos N (toFun x)

/-- Non-vacuity: the identity is an order isomorphism. -/
def OrderIso.refl (M : Mat n) : OrderIso M M :=
  ⟨⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩, fun _ => Iff.rfl⟩

/-- The inverse of a group isomorphism is again one. -/
def GroupIso.symm {m : Nat} {M : Mat n} {N : Mat m} (f : GroupIso M N) : GroupIso N M where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv
  map_add x y := by
    have h := f.map_add (f.invFun x) (f.invFun y)
    rw [f.right_inv, f.right_inv] at h
    rw [← h, f.left_inv]

/-! ### Positive integer multiples -/

/-- `nsm1 x a = (a + 1) • x`. -/
def nsm1 {M : Mat n} (x : DG M) : Nat → DG M
  | 0 => x
  | a + 1 => x + nsm1 x a

theorem nsm1_mk (M : Mat n) (u : Vec n) (k a : Nat) :
    nsm1 (mk M u k) a = mk M (vsmul ((a : Int) + 1) u) k := by
  induction a with
  | zero =>
    show mk M u k = _
    congr 1
    funext i
    simp [vsmul]
  | succ a ih =>
    show mk M u k + nsm1 (mk M u k) a = _
    rw [ih, add_same]
    congr 1
    funext i
    simp only [vadd, vsmul, Int.add_mul, Int.one_mul, Int.natCast_add, Int.natCast_one]
    omega

theorem map_nsm1 {m : Nat} {M : Mat n} {N : Mat m} (f : DG M → DG N)
    (hf : ∀ x y, f (x + y) = f x + f y) (x : DG M) (a : Nat) : f (nsm1 x a) = nsm1 (f x) a := by
  induction a with
  | zero => rfl
  | succ a ih => show f (x + nsm1 x a) = f x + nsm1 (f x) a; rw [hf, ih]

/-! ## Rank one: any two elements of a `1 × 1` dimension group are dependent -/

theorem dep_scalar (A B C D μ ν : Int) (h1 : A - C = ν) (h2 : B - D = -μ) :
    (A + 1) * μ + (B + 1) * ν = (C + 1) * μ + (D + 1) * ν := by
  obtain rfl : A = C + ν := by omega
  obtain rfl : B = D - μ := by omega
  simp only [Int.add_mul, Int.sub_mul, Int.one_mul]
  rw [Int.mul_comm ν μ]
  omega

theorem rank_one (M : Mat 1) (p q : DG M) :
    ∃ a b c d : Nat, (a ≠ c ∨ b ≠ d) ∧ nsm1 p a + nsm1 q b = nsm1 p c + nsm1 q d := by
  induction p using ind with | h u k =>
  induction q using ind with | h w l =>
  rw [mk_lift M u k l (k + l) rfl, mk_lift M w l k (k + l) (Nat.add_comm _ _)]
  generalize pw M l u = U
  generalize pw M k w = W
  generalize k + l = K
  have key : ∀ a b c d : Nat,
      (a + 1 : Int) * U 0 + (b + 1) * W 0 = (c + 1) * U 0 + (d + 1) * W 0 →
      nsm1 (mk M U K) a + nsm1 (mk M W K) b = nsm1 (mk M U K) c + nsm1 (mk M W K) d := by
    intro a b c d h
    rw [nsm1_mk, nsm1_mk, nsm1_mk, nsm1_mk, add_same, add_same]
    congr 1
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    simpa [vadd, vsmul] using h
  by_cases hU : U 0 = 0
  · refine ⟨1, 0, 0, 0, Or.inl (by decide), key _ _ _ _ ?_⟩
    rw [hU]
    simp
  · refine ⟨(W 0).toNat, (-(U 0)).toNat, (-(W 0)).toNat, (U 0).toNat, ?_, key _ _ _ _ ?_⟩
    · right
      intro h
      have h' := congrArg (fun z : Nat => (z : Int)) h
      simp only at h'
      have e1 := Int.toNat_sub_toNat_neg (U 0)
      have e2 := Int.toNat_sub_toNat_neg (-(U 0))
      rw [Int.neg_neg] at e2
      omega
    · apply dep_scalar
      · exact Int.toNat_sub_toNat_neg (W 0)
      · have e := Int.toNat_sub_toNat_neg (-(U 0))
        rw [Int.neg_neg] at e
        omega

/-! ## The two matrices -/

/-- `A = [4]`: the full 4-shift. -/
def matA : Mat 1 := fun _ _ => 4

/-- `B = [[3,1],[1,3]]`. -/
def matB : Mat 2 := fun i j => if i = j then 3 else 1

theorem rmul_matB (v : Vec 2) :
    rmul matB v = fun j => if j = 0 then 3 * v 0 + v 1 else v 0 + 3 * v 1 := by
  funext j
  have : j = 0 ∨ j = 1 := by
    rcases j with ⟨_ | _ | j, hj⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases this with rfl | rfl <;> simp [rmul, fsum, matB] <;> omega

theorem rmul_matB_inj (v w : Vec 2) (h : rmul matB v = rmul matB w) : v = w := by
  rw [rmul_matB, rmul_matB] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  funext j
  rcases j with ⟨_ | _ | j, hj⟩
  · show v 0 = w 0; omega
  · show v 1 = w 1; omega
  · omega

theorem pw_matB_inj (t : Nat) (v w : Vec 2) (h : pw matB t v = pw matB t w) : v = w := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih (rmul_matB_inj _ _ h)

/-! ## Rank two: `[e₁]`, `[e₂]` are independent in `Δ_B` -/

theorem rank_two (a b c d : Nat)
    (h : nsm1 (mk matB (basis 0) 0) a + nsm1 (mk matB (basis 1) 0) b =
      nsm1 (mk matB (basis 0) 0) c + nsm1 (mk matB (basis 1) 0) d) : a = c ∧ b = d := by
  rw [nsm1_mk, nsm1_mk, nsm1_mk, nsm1_mk, add_same, add_same, mk_eq_iff] at h
  obtain ⟨t, ht⟩ := h
  have hv := pw_matB_inj _ _ _ ht
  have e0 : ∀ x y : Int, vadd (vsmul x (basis 0)) (vsmul y (basis 1)) (0 : Fin 2) = x := by
    intro x y
    show x * (if (0 : Fin 2) = 0 then 1 else 0) + y * (if (1 : Fin 2) = 0 then 1 else 0) = x
    rw [if_pos rfl, if_neg (by decide)]
    omega
  have e1 : ∀ x y : Int, vadd (vsmul x (basis 0)) (vsmul y (basis 1)) (1 : Fin 2) = y := by
    intro x y
    show x * (if (0 : Fin 2) = 1 then 1 else 0) + y * (if (1 : Fin 2) = 1 then 1 else 0) = y
    rw [if_neg (by decide), if_pos rfl]
    omega
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  rw [e0, e0] at h0
  rw [e1, e1] at h1
  exact ⟨by omega, by omega⟩

/-- Main lemma: there is no injective additive map `Δ_B → Δ_A`. -/
theorem no_injective_hom (f : DG matB → DG matA) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hinj : ∀ x y, f x = f y → x = y) : False := by
  let x := mk matB (basis 0) 0
  let y := mk matB (basis 1) 0
  obtain ⟨a, b, c, d, hne, heq⟩ := rank_one matA (f x) (f y)
  have hf : f (nsm1 x a + nsm1 y b) = f (nsm1 x c + nsm1 y d) := by
    rw [hadd, hadd, map_nsm1 f hadd, map_nsm1 f hadd, map_nsm1 f hadd, map_nsm1 f hadd]
    exact heq
  have := rank_two a b c d (hinj _ _ hf)
  omega

theorem not_groupIso_BA : GroupIso matB matA → False := fun f =>
  no_injective_hom f.toFun f.map_add (fun x y h => by
    rw [← f.left_inv x, ← f.left_inv y, h])

/-- `Δ_A` and `Δ_B` are not isomorphic as abstract groups. -/
theorem not_groupIso_AB : GroupIso matA matB → False := fun f => not_groupIso_BA f.symm

/-- `(Δ_A, Δ_A^+)` and `(Δ_B, Δ_B^+)` are not order-isomorphic. -/
theorem not_orderIso_AB : OrderIso matA matB → False := fun f => not_groupIso_AB f.toGroupIso

/-! ## Mixing and Perron eigenvalue -/

/-- `M ≥ 0` and some power `M^k` (`k ≥ 1`) is entrywise positive (the edge shift is mixing).
The `(i, j)` entry of `M^k` is `(e_i M^k)_j`. -/
def Primitive (M : Mat n) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ ∃ k, 0 < k ∧ ∀ i j, 0 < pw M k (basis i) j

/-- `λ` has a positive (left) eigenvector: `v M = λ v` with `v > 0`.  For a nonnegative
irreducible matrix this holds exactly for the Perron eigenvalue (Perron–Frobenius). -/
def IsPerronEig (M : Mat n) (lam : Int) : Prop :=
  ∃ v : Vec n, (∀ i, 0 < v i) ∧ rmul M v = vsmul lam v

theorem fin1 (i : Fin 1) : i = 0 := Fin.ext (by omega)

theorem fin2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

theorem primitive_A : Primitive matA := by
  refine ⟨fun _ _ => by show (0 : Int) ≤ 4; decide, 1, by decide, fun i j => ?_⟩
  rw [fin1 i, fin1 j]
  decide

theorem primitive_B : Primitive matB := by
  refine ⟨fun i j => ?_, 1, by decide, fun i j => ?_⟩
  · simp only [matB]; split <;> decide
  · show 0 < rmul matB (basis i) j
    rw [rmul_matB]
    rcases fin2 i with rfl | rfl <;> rcases fin2 j with rfl | rfl <;> decide

theorem perron_A : IsPerronEig matA 4 := by
  refine ⟨fun _ => 1, fun _ => by show (0 : Int) < 1; decide, ?_⟩
  funext j
  rw [fin1 j]
  decide

theorem perron_B : IsPerronEig matB 4 := by
  refine ⟨fun _ => 1, fun _ => by show (0 : Int) < 1; decide, ?_⟩
  rw [rmul_matB]
  funext j
  rcases fin2 j with rfl | rfl <;> decide

/-- The other eigenvalue of `B` is `2` (eigenvector `(1,-1)`), so spec `B = {4, 2}` and `4`
is the spectral radius. -/
theorem second_eig_B : rmul matB (fun j => if j = 0 then 1 else -1) =
    vsmul 2 (fun j => if j = 0 then 1 else -1) := by
  rw [rmul_matB]
  funext j
  rcases fin2 j with rfl | rfl <;> decide

/-- Number of paths of length `k` in the graph of `M` = sum of the entries of `M^k`. -/
def pathCount (M : Mat n) (k : Nat) : Int := fsum n (fun i => fsum n (fun j => pw M k (basis i) j))

/-- `X_A` and `X_B` have the same growth `4^k` (entropy `log 4`). -/
theorem pathCount_A (k : Nat) : pathCount matA k = 4 ^ k := by
  have h : ∀ k (v : Vec 1), pw matA k v 0 = 4 ^ k * v 0 := by
    intro k
    induction k with
    | zero => intro v; show v 0 = 4 ^ 0 * v 0; simp
    | succ k ih =>
      intro v
      show fsum 1 (fun i => pw matA k v i * matA i 0) = 4 ^ (k + 1) * v 0
      simp only [fsum, matA]
      rw [ih, Int.pow_succ]
      generalize (4 : Int) ^ k = p
      rw [Int.add_zero, Int.mul_assoc, Int.mul_assoc, Int.mul_comm (v 0) 4]
  show fsum 1 (fun i => fsum 1 (fun j => pw matA k (basis i) j)) = 4 ^ k
  simp only [fsum]
  rw [h]
  simp [basis]

theorem pathCount_B (k : Nat) : pathCount matB k = 2 * 4 ^ k := by
  have h : ∀ k (v : Vec 2), fsum 2 (pw matB k v) = 4 ^ k * fsum 2 v := by
    intro k
    induction k with
    | zero => intro v; show fsum 2 v = 4 ^ 0 * fsum 2 v; simp
    | succ k ih =>
      intro v
      show fsum 2 (rmul matB (pw matB k v)) = _
      have e : fsum 2 (rmul matB (pw matB k v)) = 4 * fsum 2 (pw matB k v) := by
        rw [rmul_matB]
        simp [fsum]
        omega
      rw [e, ih, Int.pow_succ]
      generalize fsum 2 v = s
      generalize (4 : Int) ^ k = p
      rw [Int.mul_comm p 4, Int.mul_assoc]
  show fsum 2 (fun i => fsum 2 (pw matB k (basis i))) = _
  simp only [h]
  simp [fsum, basis]
  omega

/-! ## The conjecture -/

/-- The "if" direction of the conjecture for mixing SFTs given by integer matrices with
integer Perron eigenvalues, where `Cond λ_A λ_B` is *any* reading of "`λ_A` and `λ_B`
generate the same real number field with agreeing unit group cosets". -/
def IfDirection (Cond : Int → Int → Prop) : Prop :=
  ∀ (n m : Nat) (A : Mat n) (B : Mat m) (lA lB : Int),
    Primitive A → Primitive B → IsPerronEig A lA → IsPerronEig B lB → Cond lA lB →
    Nonempty (OrderIso A B)

/-- The full biconditional, for a reading `Cond`. -/
def Conjecture (Cond : Int → Int → Prop) : Prop :=
  ∀ (n m : Nat) (A : Mat n) (B : Mat m) (lA lB : Int),
    Primitive A → Primitive B → IsPerronEig A lA → IsPerronEig B lB →
    (Nonempty (OrderIso A B) ↔ Cond lA lB)

/-- Every reading of the right-hand side holds when `λ_A = λ_B` (reflexivity), and then the
"if" direction fails for `A = [4]`, `B = [[3,1],[1,3]]`. -/
theorem conjecture_00000009614_false (Cond : Int → Int → Prop) (hrefl : ∀ x, Cond x x) :
    ¬ IfDirection Cond := fun h =>
  match h 1 2 matA matB 4 4 primitive_A primitive_B perron_A perron_B (hrefl 4) with
  | ⟨f⟩ => not_orderIso_AB f

theorem conjecture_00000009614_iff_false (Cond : Int → Int → Prop) (hrefl : ∀ x, Cond x x) :
    ¬ Conjecture Cond := fun h =>
  conjecture_00000009614_false Cond hrefl
    (fun n m A B lA lB hA hB pA pB hc => (h n m A B lA lB hA hB pA pB).2 hc)

/-- Even the weakest notion (abstract group isomorphism) fails. -/
theorem conjecture_00000009614_group_false (Cond : Int → Int → Prop) (hrefl : ∀ x, Cond x x) :
    ¬ (∀ (n m : Nat) (A : Mat n) (B : Mat m) (lA lB : Int),
      Primitive A → Primitive B → IsPerronEig A lA → IsPerronEig B lB → Cond lA lB →
      Nonempty (GroupIso A B)) := fun h =>
  match h 1 2 matA matB 4 4 primitive_A primitive_B perron_A perron_B (hrefl 4) with
  | ⟨f⟩ => not_groupIso_AB f

/-- A concrete reading: the field is `ℚ(λ)`; for rational integers this is `ℚ` for both,
whose unit group is `{±1}`, so "agreeing unit cosets" means `λ_A = ± λ_B`. -/
def CondQ (a b : Int) : Prop := a = b ∨ a = -b

theorem conjecture_00000009614_false_Q : ¬ IfDirection CondQ :=
  conjecture_00000009614_false CondQ (fun _ => Or.inl rfl)

/-- Non-vacuity: the hypotheses are satisfiable, and order isomorphisms exist. -/
theorem nonvacuous : Primitive matA ∧ Primitive matB ∧ IsPerronEig matA 4 ∧ IsPerronEig matB 4 ∧
    Nonempty (OrderIso matA matA) ∧ Nonempty (OrderIso matB matB) :=
  ⟨primitive_A, primitive_B, perron_A, perron_B, ⟨OrderIso.refl _⟩, ⟨OrderIso.refl _⟩⟩

end DimGroup

#print axioms DimGroup.add_assoc'
#print axioms DimGroup.neg_add'
#print axioms DimGroup.rank_one
#print axioms DimGroup.rank_two
#print axioms DimGroup.no_injective_hom
#print axioms DimGroup.not_orderIso_AB
#print axioms DimGroup.pathCount_B
#print axioms DimGroup.conjecture_00000009614_false
#print axioms DimGroup.conjecture_00000009614_iff_false
#print axioms DimGroup.conjecture_00000009614_group_false
#print axioms DimGroup.nonvacuous
