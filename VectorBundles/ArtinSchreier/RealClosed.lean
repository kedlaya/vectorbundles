module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

lemma odd_irreducible_factor {F : Type} [Field F] (f : Polynomial F)
  (h : Odd f.natDegree) : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
    have _ : f ≠ 0 := by
      unfold Odd at h
      obtain ⟨k, _⟩ := h
      have t : f.natDegree > 0 := by
        grind
      exact Polynomial.ne_zero_of_natDegree_gt t
    let S := UniqueFactorizationMonoid.factors f
    have h_prod : Associated S.prod f := by
      apply UniqueFactorizationMonoid.factors_prod
      grind
    have _ : 0 ∉ S := by
      by_contra
      have hS : S.prod = 0 := by
        exact Multiset.prod_eq_zero this
      have _ : Associated 0 f := by
        grind
      have _ : Associated f 0 := by
        grind [Associated.symm]
      have _ : Associated f 0 ↔ f = 0 :=
        associated_zero_iff_eq_zero f
      grind
    have _ : S.prod.degree = f.degree := by
      exact Polynomial.degree_eq_degree_of_associated h_prod
    have _ : S.prod.natDegree = f.natDegree := by
      (expose_names; exact Polynomial.natDegree_eq_of_degree_eq h_3)
    have _ : Odd S.prod.natDegree := by
      grind
    have hg : ∃ g ∈ S, Odd g.natDegree := by
      by_contra
      let T := S.map Polynomial.natDegree
      have _ : S.prod.natDegree = T.sum := by
        apply Polynomial.natDegree_multiset_prod
        grind
      have h_even : ∀ g ∈ S, Even g.natDegree := by
        grind
      have ht : ∀ t : ℕ, t ∈ T → Even t := by
        by_contra
        push Not at this
        obtain ⟨t, ht1, ht2⟩ := this
        unfold Multiset.map at T
        have hg : ∃ g ∈ S, g.natDegree = t := by
          exact Multiset.mem_map.mp ht1
        obtain ⟨g, hg⟩ := hg
        grind
      have _ : 2 ∣ T.sum := by
        apply Multiset.dvd_sum
        unfold Even at ht
        intro x hx
        specialize ht x
        simp_all
        obtain ⟨r, ht⟩ := ht
        have _ : x = 2*r := by
          grind
        (expose_names; exact dvd_of_mul_right_eq r (id (Eq.symm h_6)))
      grind
    obtain ⟨g, hg1, hg2⟩ := hg
    use g
    constructor
    · unfold S at hg1
      exact UniqueFactorizationMonoid.irreducible_of_factor g hg1
    constructor
    · exact UniqueFactorizationMonoid.dvd_of_mem_factors hg1
    apply hg2

lemma tmp (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] (a b: F) :
  (algebraMap F K) a * (algebraMap F K) b = (algebraMap F K) (a*b) := by
  grind

lemma tmp2 (F : Type) (K : Type) [Field F] [Field K] [Algebra F K] (a b: F) :
  (algebraMap F K) a + (algebraMap F K) b = (algebraMap F K) (a + b) := by
  grind

lemma RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h1 : ∀ i : F, i^2 ≠ -1)
  (h2 : ∃ i : K, i^2 = -1 ∧ ∀ x : K, x ∈ (algebraMap (IntermediateField.adjoin F {x : K | x = i}) K).range)
  : IsRealClosed F := by

  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i

  let iota := algebraMap F K

  have real_imag: ∀ (u : K), ∃ a : F, ∃ b : F, u = iota a + i * iota b := by
    sorry

  have real_imag_unique: ∀ (a₁ b₁ a₂ b₂ : F),
    iota a₁ + i * iota b₁ = iota a₂ + i * iota b₂
    → a₁ = a₂ ∧ b₁ = b₂ := by
    by_contra
    push Not at this
    obtain ⟨a₁, b₁, a₂, b₂, h1, h2⟩ := this
    have hm : iota (a₁ - a₂) =  i * iota (b₂ - b₁) := by
      grind
    by_cases h3: b₁ = b₂
    · have _ : 0 = iota (a₂ - a₁) := by
        grind
      have _ : a₂ - a₁ = 0 := by
        apply FaithfulSMul.algebraMap_injective F K
        grind
      grind
    · let c := (a₁ - a₂)/ (b₂ - b₁)
      have _ :  i * iota (b₂ - b₁) = iota (c * (b₂ - b₁)) := by
        grind
      have _ : iota (c * (b₂ - b₁)) = iota (c) * iota (b₂ - b₁) := by
        exact algebraMap.coe_mul c (b₂ - b₁)
      have _ : i * iota (b₂ - b₁) = iota (c) * iota (b₂ - b₁) := by
        grind
      have _ : iota (b₂ - b₁) ≠ 0 := by
        grind [FaithfulSMul.algebraMap_injective F K]
      have _ : i = iota c := by
        grind
      simp_all
      sorry

  have h_alg : ∀ (a b : F), (iota a) * (iota b) = iota (a*b) := by grind

  have semi: IsSemireal F := by
    have hs: ∀ x : F, ∀ y : F, ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have have_u: ∃ u : K, u^2 = iota x + i * iota y := by
        apply IsAlgClosed.exists_pow_nat_eq
        simp
      obtain ⟨u, hu⟩ := have_u
      let have_ab := real_imag
      specialize have_ab u
      obtain ⟨a, b, hab⟩ := have_ab
      have _ : iota (a*a) - iota (b * b) = iota (a^2 - b^2) := by
        sorry
      have _ : 2 * iota a * iota b = iota (2 * a * b) := by
        have _ : iota a * iota b = iota (a * b) := by
          exact tmp F K a b
        have _ : iota 2 * iota (a * b) = iota (2 * (a * b)) :=
          tmp F K 2 (a*b)
        have _ : iota 1 + iota 1 = iota (1 + 1) :=
          tmp2 F K 1 1
        sorry
      have _ : u * u = iota (a ^ 2 - b ^ 2) + i * iota (2 * a * b) := by
        calc u * u = (iota a + i * iota b)^2 :=  by grind
        _ = iota a * iota a + 2 * i * iota a * iota b - iota b * iota b := by grind
        _ = iota (a*a) + 2 * i * iota a * iota b - iota b * iota b :=
          sub_left_inj.mpr (congrFun (congrArg HAdd.hAdd (h_alg a a)) (2 * i * iota a * iota b))
        _ = iota (a*a) + 2 * i * iota a * iota b - iota (b * b) :=
          sub_right_inj.mpr (h_alg b b)
        _ = iota (a ^ 2 - b ^ 2) + i * iota (2 * a * b) := by grind
      let have_ab_unique := real_imag_unique
      specialize have_ab_unique (a ^ 2 - b ^ 2) (2 * a * b) x y
      have _ : a ^ 2 - b ^ 2 = x ∧ 2 * a * b = y := by
        grind
      use a ^ 2 + b ^ 2
      grind
    have hssq: ∀ x : F, IsSumSq x → IsSquare x := by
      intro x hx
      induction hx with
      | zero => simp
      | sq_add y _ hz =>
          rcases hz with ⟨z, hz⟩
          unfold IsSquare
          subst hz
          obtain ⟨r, hr⟩ := hs y z
          use r
          grind
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    have h2 : IsSquare (-1 : F) := by
      grind
    sorry

  have hR: CharZero F := by
    exact CharP.charP_to_charZero F

  have issquare: ∀ (x : F), IsSquare x ∨ IsSquare (-x) := by
    intro x
    have h_sqrtx : ∃ y : K, y^2 = iota x := by
      apply IsAlgClosed.exists_pow_nat_eq
      simp
    obtain ⟨y, h_sqrtx⟩ := h_sqrtx
    let have_ab := real_imag
    specialize have_ab y
    obtain ⟨a, b, have_ab⟩ := have_ab
    let have_ab_unique := real_imag_unique
    specialize have_ab_unique (a^2-b^2) (2*a*b) x 0
    have h_reim : a^2 - b^2 = x ∧ 2*a*b = 0 := by
      sorry
    obtain ⟨h_re, h_im⟩ := h_reim
    have ab_zero : a = 0 ∨ b = 0 := by
      refine zero_eq_mul.mp ?_
      grind
    cases ab_zero with
    | inl a_zero =>
      right
      unfold IsSquare
      use b
      grind
    | inr b_zero =>
      left
      unfold IsSquare
      use a
      grind

  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    have _ : ∀ f : Polynomial F, Irreducible f → f.natDegree ≤ 2 := by
      by_contra
      push Not at this
      obtain ⟨f, h1, h2⟩ := this
      have h_x : ∃ x : K, Polynomial.aeval x f = 0 := by
        sorry
      obtain ⟨x, h_x⟩ := h_x
      let have_ab := real_imag
      specialize have_ab x
      obtain ⟨a, b, hab⟩ := have_ab
      sorry
    intro f h_odd
    have h_g : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
      odd_irreducible_factor f h_odd
    obtain ⟨g, h_irr, h_div, h_odd⟩ := h_g
    have _ : g.natDegree ≤ 2 := by
      (expose_names; exact String.Pos.Raw.mk_le_mk.mp (h g h_irr))
    have h_natgdeg : g.natDegree = 1 := by
      grind
    have h_gdeg : g.degree = g.natDegree := by
      refine Polynomial.degree_eq_natDegree ?_
      exact Irreducible.ne_zero h_irr
    have h_x : ∃ x : F, g.IsRoot x := by
      refine Polynomial.exists_root_of_degree_eq_one ?_
      calc
        g.degree = g.natDegree := h_gdeg
        _ = 1 := Nat.cast_eq_one.mpr h_natgdeg
    obtain ⟨x, h_x⟩ := h_x
    use x
    exact Polynomial.IsRoot.dvd h_x h_div

  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare, exists_isRoot_of_odd_natDegree := odd_deg }
