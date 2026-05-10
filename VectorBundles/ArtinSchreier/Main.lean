module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Finset.Defs
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
-- public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2
public import VectorBundles.ArtinSchreier.ArtinSchreier3
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

theorem artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosure F K] : IsAlgClosed F ∨ IsRealClosed F := by
  have _: IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  have have_i: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp -- to prove 0 < 2
  obtain ⟨i, hi⟩ := have_i
  if hF : i ∈ (algebraMap F K).range then
    left
    apply finite_algebraic_closure_with_i F K
    have hj : ∃ j : F, (algebraMap F K) j = i := by
      exact Set.mem_range.mp hF
    obtain ⟨j, hj⟩ := hj
    have _ : j^2 = -1 := by
      have _ : Function.Injective (algebraMap F K) := by
        exact FaithfulSMul.algebraMap_injective F K
      have _ : (algebraMap F K) (j^2) = (algebraMap F K) (-1) := by
        simp_all
      grind
    use j
  else
    right
    let S : Set K := {x | x = i}
    let F₁ := IntermediateField.adjoin F S
    have _ : i ∈ F₁ := by
      have hiS: i ∈ S := by
        exact Set.mem_setOf.mpr rfl
      exact IntermediateField.mem_adjoin_of_mem F hiS
    let iota₁ := algebraMap F₁ K
    have _: IsAlgClosure F₁ K := by
      apply IsAlgClosure.ofAlgebraic F₁ K
    have _: IsAlgClosed F₁ := by
      apply finite_algebraic_closure_with_i F₁ K
      have hj : ∃ j : F₁, iota₁ j = i := by
        (expose_names; exact CanLift.prf i h_1)
      obtain ⟨j, hj⟩ := hj
      have _ : j^2 = -1 := by
        have _ : Function.Injective iota₁ := by
          exact FaithfulSMul.algebraMap_injective (↥F₁) K
        have _ : iota₁ (j^2) = iota₁ (-1) := by
          simp_all
        grind
      use j
    have hF1 : ∀ x : K, x ∈ (algebraMap F₁ K).range := by
      have _ : ∀ x : K, (minpoly F₁ x).degree = 1 := by
        intro x
        let pol := minpoly F₁ x
        have hirr : Irreducible pol := by
          apply minpoly.irreducible
          exact Algebra.IsIntegral.isIntegral x
        exact IsAlgClosed.degree_eq_one_of_irreducible (↥F₁) hirr
      (expose_names; exact fun x => minpoly.mem_range_of_degree_eq_one (↥F₁) x (h_4 x))
    have _ : ∀ i : F, i^2 ≠ -1 := by
      by_contra
      push Not at this
      obtain ⟨j, hj⟩ := this
      have _ : (algebraMap F K) (j^2) = ((algebraMap F K) j)^2 := by
        exact algebraMap.coe_pow j 2
      have _ : ((algebraMap F K) j + i) * ((algebraMap F K) j - i) = 0 := by
        grind
      have h3 : (algebraMap F K) j + i = 0 ∨ (algebraMap F K) j - i = 0 := by
        (expose_names; exact zero_eq_mul.mp (id (Eq.symm h_5)))
      have _ : ∃ k : F, (algebraMap F K) k = i := by
        cases h3
        use -j
        grind
        use j
        grind
      apply hF
      simp_all
    apply RealClosed_from_quadratic F K
    · simp_all
    · use i
