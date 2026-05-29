module

public import Mathlib.FieldTheory.IntermediateField.Basic
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
  let F₁ := F⟮i⟯
  have h_iF1 : i ∈ F₁ := mem_adjoin_simple_self F i
  let iota₁ := algebraMap F₁ K
  have : IsAlgClosure F₁ K := by
    apply IsAlgClosure.ofAlgebraic F₁ K
  have : IsAlgClosed F₁ := by
    apply finite_algebraic_closure_with_i F₁ K
    have hj : ∃ j : F₁, iota₁ j = i := CanLift.prf i h_iF1
    obtain ⟨j, hj⟩ := hj
    have : j^2 = -1 := by
      have : Function.Injective iota₁ := FaithfulSMul.algebraMap_injective (↥F₁) K
      have : iota₁ (j^2) = iota₁ (-1) := by simp_all
      grind
    use j
  have : IsAlgClosure F₁ F₁ := IsAlgClosed.instIsAlgClosure ↥F₁
  if hF : ∃ j : F, j^2 = -1 then
    left
    apply finite_algebraic_closure_with_i F K hF
  else
    right
    have _ : ∀ i : F, i^2 ≠ -1 := by
      by_contra
      push Not at this
      obtain ⟨j, hj⟩ := this
      have _ : iota (j^2) = (iota j)^2 :=
        algebraMap.coe_pow j 2
      have h3 : iota j + i = 0 ∨ iota j - i = 0 := by grind
      have _ : ∃ k : F, iota k = i := by
        cases h3
        · use -j
          grind
        · use j
          grind
      apply hF
      simp_all
    have hF1 : ∀ x : K, x ∈ iota₁.range :=
      have h_deg1 : ∀ x : K, (minpoly F₁ x).degree = 1 := by
        intro x
        let pol := minpoly F₁ x
        have hirr : Irreducible pol := minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
        exact IsAlgClosed.degree_eq_one_of_irreducible (↥F₁) hirr
      fun x => minpoly.mem_range_of_degree_eq_one (↥F₁) x (h_deg1 x)
    apply RealClosed_from_quadratic F K
    · simp_all
    · use i
      constructor
      · exact hi
      · refine (ext ?_).symm
        intro x
        constructor
        · aesop
        · simp_all
