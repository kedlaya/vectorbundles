module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic

public import VectorBundles.ArtinSchreier.ArtinSchreier3
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

open IntermediateField

theorem artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  have _: IsAlgClosed K := IsAlgClosure.isAlgClosed F
  let iota := algebraMap F K
  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i
  if hF : i ∈ iota.range then
    left
    apply finite_algebraic_closure_with_i F K
    have hj : ∃ j : F, iota j = i := Set.mem_range.mp hF
    obtain ⟨j, hj⟩ := hj
    have _ : j^2 = -1 := by
      have _ : Function.Injective iota := FaithfulSMul.algebraMap_injective F K
      have _ : iota (j^2) = iota (-1) := by
        simp_all
      grind
    use j
  else
    right
    let F₁ := F⟮i⟯
    have h_iF1 : i ∈ F₁ := mem_adjoin_simple_self F i
    let iota₁ := algebraMap F₁ K
    have _: IsAlgClosure F₁ K := by
      apply IsAlgClosure.ofAlgebraic F₁ K
    have _: IsAlgClosed F₁ := by
      apply finite_algebraic_closure_with_i F₁ K
      have hj : ∃ j : F₁, iota₁ j = i := CanLift.prf i h_iF1
      obtain ⟨j, hj⟩ := hj
      have _ : j^2 = -1 := by
        have _ : Function.Injective iota₁ := by
          exact FaithfulSMul.algebraMap_injective (↥F₁) K
        have _ : iota₁ (j^2) = iota₁ (-1) := by
          simp_all
        grind
      use j
    have _ : IsAlgClosure F₁ F₁ := IsAlgClosed.instIsAlgClosure ↥F₁
    have _ : ∀ i : F, i^2 ≠ -1 := by
      by_contra
      push Not at this
      obtain ⟨j, hj⟩ := this
      have _ : iota (j^2) = (iota j)^2 :=
        algebraMap.coe_pow j 2
      have h2 : (iota j + i) * (iota j - i) = 0 := by
        grind
      have h3 : iota j + i = 0 ∨ iota j - i = 0 :=
        zero_eq_mul.mp (id h2.symm)
      have _ : ∃ k : F, iota k = i := by
        cases h3
        · use -j
          grind
        · use j
          grind
      apply hF
      simp_all
    have hF1 : ∀ x : K, x ∈ (algebraMap F₁ K).range :=
      have h_deg1 : ∀ x : K, (minpoly F₁ x).degree = 1 := by
        intro x
        let pol := minpoly F₁ x
        have hirr : Irreducible pol :=
          minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
        exact IsAlgClosed.degree_eq_one_of_irreducible (↥F₁) hirr
      fun x => minpoly.mem_range_of_degree_eq_one (↥F₁) x (h_deg1 x)
    have _ : F₁ = ⊤ := by
      refine (ext ?_).symm
      intro x
      constructor
      · simp_all
      · simp_all
    apply RealClosed_from_quadratic F K
    · simp_all
    · use i
