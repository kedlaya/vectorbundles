module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.CharP.Defs
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
public import Mathlib.FieldTheory.Relrank

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2
public import VectorBundles.ArtinSchreier.ArtinSchreier3
public import VectorBundles.ArtinSchreier.ArtinSchreier4
public import VectorBundles.ArtinSchreier.RealClosed

@[expose] public section

open IntermediateField

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
    let F₁ := F⟮i⟯
    have h_iF1 : i ∈ F₁ :=
      mem_adjoin_simple_self F i
    let iota₁ := algebraMap F₁ K
    have _: IsAlgClosure F₁ K := by
      apply IsAlgClosure.ofAlgebraic F₁ K
    have _: IsAlgClosed F₁ := by
      apply finite_algebraic_closure_with_i F₁ K
      have hj : ∃ j : F₁, iota₁ j = i :=
        CanLift.prf i h_iF1
      obtain ⟨j, hj⟩ := hj
      have _ : j^2 = -1 := by
        have _ : Function.Injective iota₁ := by
          exact FaithfulSMul.algebraMap_injective (↥F₁) K
        have _ : iota₁ (j^2) = iota₁ (-1) := by
          simp_all
        grind
      use j
    have _ : IsAlgClosure F₁ F₁ := by
      exact IsAlgClosed.instIsAlgClosure ↥F₁
    have _ : ∀ i : F, i^2 ≠ -1 := by
      by_contra
      push Not at this
      obtain ⟨j, hj⟩ := this
      have _ : (algebraMap F K) (j^2) = ((algebraMap F K) j)^2 := by
        exact algebraMap.coe_pow j 2
      have h2 : ((algebraMap F K) j + i) * ((algebraMap F K) j - i) = 0 := by
        grind
      have h3 : (algebraMap F K) j + i = 0 ∨ (algebraMap F K) j - i = 0 := by
        (expose_names; exact zero_eq_mul.mp (id (Eq.symm h2)))
      have _ : ∃ k : F, (algebraMap F K) k = i := by
        cases h3
        · use -j
          grind
        · use j
          grind
      apply hF
      simp_all
    have hF1 : ∀ x : K, x ∈ (algebraMap F₁ K).range := by
      have h_deg1 : ∀ x : K, (minpoly F₁ x).degree = 1 := by
        intro x
        let pol := minpoly F₁ x
        have hirr : Irreducible pol := by
          apply minpoly.irreducible
          exact Algebra.IsIntegral.isIntegral x
        exact IsAlgClosed.degree_eq_one_of_irreducible (↥F₁) hirr
      exact fun x => minpoly.mem_range_of_degree_eq_one (↥F₁) x (h_deg1 x)
    have _ : F₁ = ⊤ := by
      refine Eq.symm (ext ?_)
      intro x
      constructor
      · simp_all
      · simp_all
    apply RealClosed_from_quadratic F K
    · simp_all
    · use i
