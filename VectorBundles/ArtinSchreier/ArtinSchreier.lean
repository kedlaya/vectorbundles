module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

lemma finite_algebraic_closure_separable (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsGalois F K :=
  have _: PerfectField F := by
    by_cases CharZero F
    · apply PerfectField.ofCharZero
    · let p := ringChar F
      have _: Nat.Prime p ∨ p = 0 := by
        apply CharP.char_is_prime_or_zero F p
      have _: Nat.Prime p := by
        grind [CharP.ringChar_zero_iff_CharZero F]
      have _: ExpChar F p := by
        (expose_names; exact ExpChar.prime h_2)
      let frob := frobenius F p
      have _: Function.Surjective frob := by
        unfold Function.Surjective
        unfold frob
        intro a
        let d := Module.finrank F K
        have _ : 1 < p := by
          (expose_names; exact Nat.Prime.one_lt h_2)
        have h1: ∃ n : ℕ, d < p^n := by
          refine pow_unbounded_of_one_lt d ?_
          grind
        obtain ⟨n, h2⟩ := h1
        have _: IsAlgClosed K := by
          exact IsAlgClosure.isAlgClosed F
        have h3: ∃ b : K, b^(p^n) = (algebraMap F K) a := by
          refine IsAlgClosed.exists_pow_nat_eq ((algebraMap F K) a) ?_
          grind
        obtain ⟨b, h4⟩ := h3
        let f := minpoly F b
        have _ : ¬ Irreducible f := by
          sorry
        let g := Polynomial.factor f
        let d₁ := Polynomial.natDegree g
        have _ : d₁ < p^n := by
          sorry
        let e := gcd d₁ p^n
        let (g_1, g_2) := Nat.xgcd d₁ p^n
        sorry
      have _: PerfectRing F p := by
        (expose_names; exact PerfectRing.ofSurjective F p h_4)
      exact PerfectRing.toPerfectField F p
  { to_isSeparable := IsSepClosure.isSeparable, to_normal := IsGalois.to_normal }

lemma finite_algebraic_closure_cyclic_prime (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (h: Module.finrank F K = p)
  (hsep: IsGalois F K): ¬ ringChar F = p := by
  sorry

lemma finite_algebraic_closure_cyclic_quadratic (F : Type) (K : Type) (p : ℕ)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (hp: Nat.Prime p) (hrank: Module.finrank F K = p)
  (hgal: IsGalois F K): p = 2 := by
  sorry

lemma quadratic_algebraic_closure_no_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : Module.finrank F K = 2) : ¬∃ (i : F), i^2 = -1 := by
  sorry

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by

  by_contra
  have hgal: IsGalois F K :=
    finite_algebraic_closure_separable F K
  let G := K ≃ₐ[F] K
  let d := Nat.card G
  have hd : 1 < d := by
    -- apply IsGaloisGroup.card_eq_finrank
    sorry
  let p := Nat.minFac d
  have hp : Nat.Prime p := by
    sorry
    --apply Nat.minFac_prime d hd
  have cyc: ∃ (g : G), orderOf g = p := by
    -- apply exists_prime_orderOf_dvd_card p
    sorry
  obtain ⟨g, hg1⟩ := cyc
  let H := Subgroup.zpowers g
  let F₁ := IntermediateField.fixedField H
  have hrank : Module.finrank F₁ K = p := by
    sorry
    --apply IsGalois.card_fixingSubgroup_eq_finrank
  have _: IsAlgClosure F₁ K := by
    sorry
  have hgal1: IsGalois F₁ K :=
    finite_algebraic_closure_separable F₁ K
  have hp2: p = 2 :=
      finite_algebraic_closure_cyclic_quadratic F₁ K p hp hrank hgal1
  apply quadratic_algebraic_closure_no_i F₁ K
  grind
  rcases h with ⟨i, hi⟩
  let iota := algebraMap F F₁
  have h2 : Function.Injective iota := by
    exact FaithfulSMul.algebraMap_injective F ↥F₁
  let i₁ := iota i
  use i₁
  sorry

lemma RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h : Module.finrank F K = 2) (h1 : ¬ ∃ i : F, i^2 = -1) : IsRealClosed F := by

  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i

  have semi: IsSemireal F := by
    have hs: ∀ x : F, ∀ y : F, ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have have_u: ∃ u : K, u^2 = ⇑(algebraMap F K) x + i * ⇑(algebraMap F K) y := by
        sorry
      obtain ⟨u, hu⟩ := have_u
      have have_ab: ∃ a : F, ∃ b : F, u = ⇑(algebraMap F K) a + i * ⇑(algebraMap F K) b := by
        sorry
      obtain ⟨a, b, hab⟩ := have_ab
      use a^2 + b^2
      sorry
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
    obtain ⟨a,b⟩ := h2
    apply h1
    use a
    grind
  have hR: CharZero F := by
    exact CharP.charP_to_charZero F
  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := ?_, exists_isRoot_of_odd_natDegree := ?_ }
  -- ∀ (x : F), IsSquare x ∨ IsSquare (-x)
  sorry
  -- ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x
  intro f
  let p := f.roots
  let G := K ≃ₐ[F] K
  sorry

theorem artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  have _: IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  if hi: ∃ i : F, i^2 = -1 then
    left
    apply finite_algebraic_closure_with_i F K hi
  else
    right
    have have_i: ∃ i : K, i^2 = -1 := by
      apply IsAlgClosed.exists_pow_nat_eq
      simp -- to prove 0 < 2
    obtain ⟨i, hi⟩ := have_i
    let S : Set K := {x : K | x = i}
    let F₁ := IntermediateField.adjoin F S
    have hFi: ∃ i₁ : F₁, ⇑(algebraMap F₁ K) i₁ = i := by
      sorry
    obtain ⟨i₁, hi₁⟩ := hFi
    have hACF: IsAlgClosed F₁ := by
      have _: IsAlgClosure F₁ K := by
        sorry
      apply finite_algebraic_closure_with_i F₁ K
      use i₁
      sorry
    apply RealClosed_from_quadratic F F₁
    sorry -- [F₁:F] = 2
    grind
