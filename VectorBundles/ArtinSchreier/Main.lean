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
  have : IsAlgClosure F₁ K := by apply IsAlgClosure.ofAlgebraic F₁ K
  have : IsAlgClosed F₁ := by
    apply finite_algebraic_closure_with_i F₁ K
    have hj : ∃ j : F₁, iota₁ j = i := CanLift.prf i h_iF1
    obtain ⟨j, hj⟩ := hj
    use j
    have : Function.Injective iota₁ := FaithfulSMul.algebraMap_injective (↥F₁) K
    have : iota₁ (j^2) = iota₁ (-1) := by simp_all
    grind
  if hF : ∃ j : F, j^2 = -1 then
    left
    apply finite_algebraic_closure_with_i F K hF
  else
    right
    apply RealClosed_from_quadratic F K
    · push Not at hF
      exact hF
    · use i
      refine ⟨hi, ?_⟩
      refine (ext ?_).symm
      intro x
      constructor
      · intro hx
        have h_deg1 : (minpoly F₁ x).degree = 1 :=
          have hirr : Irreducible (minpoly F₁ x) := minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
          IsAlgClosed.degree_eq_one_of_irreducible (↥F₁) hirr
        refine IsIntegral.mem_intermediateField_of_minpoly_splits ?_ ?_
        · exact Algebra.IsIntegral.isIntegral x
        · exact IsAlgClosed.splits (Polynomial.map (algebraMap F ↥F⟮i⟯) (minpoly F x))
      · exact fun a => mem_top
