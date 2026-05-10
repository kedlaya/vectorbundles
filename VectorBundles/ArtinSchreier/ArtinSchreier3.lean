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
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier
public import VectorBundles.ArtinSchreier.ArtinSchreier2
public import VectorBundles.ArtinSchreier.FieldTheory

@[expose] public section

open IntermediateField

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

lemma finite_separable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  have _ : IsGalois F K := by
    (expose_names; exact { to_isSeparable := inst_4, to_normal := IsAlgClosure.normal F K })
  let G := Gal(K/F)
  have hG : Nat.card G = 1 := by
    by_contra
    let d := Nat.card G
    have hp : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d := by
      exact Nat.exists_prime_and_dvd this
    obtain ⟨p, hp1, hp2⟩ := hp
    have hp2 : Fact (Nat.Prime p) := by
      exact fact_iff.mpr hp1
    have hp3 : Fact (p.Prime) := by
      exact fact_iff.mpr hp1
    have hg : ∃ g : G, orderOf g = p := by
      apply exists_prime_orderOf_dvd_card
      have _ : Nat.card G = Fintype.card G := by
        exact Nat.card_eq_fintype_card
      subst d
      simp_all
    obtain ⟨g, hg⟩ := hg
    let H := Subgroup.zpowers g
    let E := IntermediateField.fixedField H
    have _ : Nat.card H = p := by
      sorry
    have h_ekrank : Module.finrank E K = p := by
      sorry
    have _ : IsAlgClosure E K := by
      refine { isAlgClosed := ?_, isAlgebraic := ?_ }
      exact IsAlgClosure.isAlgClosed F
      exact IntermediateField.isAlgebraic_tower_top
    have hgal: IsGalois E K := by
      exact IsGalois.tower_top_intermediateField E
    have _ : p = 2 := by
      apply finite_algebraic_closure_cyclic_quadratic E K
      exact hp1
      exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm h_ekrank))))
      apply hgal
    have h_char2 : ringChar E ≠ 2 := by
      apply finite_algebraic_closure_cyclic_prime E K
      simp_all
      simp_all
      exact hgal
    have h_sq : ∀ (a : E), IsSquare a := by
      have h_sq1 : ∀ (a : E), IsSquare a ∨ IsSquare (-a) := by
        apply quadratic_algebraic_closure_no_i E K
        simp_all
      sorry
    have _ : FiniteDimensional E K := by
      exact finiteDimensional_right E
    have h_sq3 : ∃ (a: E), ¬ IsSquare a := by
      apply nonsquare_in_quadratic_extension E K
      simp_all
      exact h_char2
    simp_all
  exact trivial_absolute_galois_group F K hG

lemma finite_inseparable_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsPurelyInseparable F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  sorry

lemma finite_algebraic_closure_with_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : ∃ (i : F), i^2 = -1) : IsAlgClosed F := by
  obtain ⟨i, hi⟩ := h
  let E := separableClosure F K
  have _ : IsPurelyInseparable E K := by
    exact separableClosure.isPurelyInseparable F K
  have _ : IsAlgClosure E K := by
    refine { isAlgClosed := ?_, isAlgebraic := ?_ }
    exact IsAlgClosure.isAlgClosed F
    exact IntermediateField.isAlgebraic_tower_top
  have _ : IsAlgClosed E := by
    apply finite_inseparable_algebraic_closure_with_i E K
    use (algebraMap F E) i
    have _ : (algebraMap F E) (i^2) = (algebraMap F E) (-1) := by
      grind
    have _ : (algebraMap F E) (-1) = -1 := by
      grind
    grind
  have _ : IsAlgClosure F E := by
    refine { isAlgClosed := ?_, isAlgebraic := ?_ }
    exact IsSepClosed.isAlgClosed_of_perfectField ↥E
    exact separableClosure.isAlgebraic F K
  apply finite_separable_algebraic_closure_with_i F E
  use i
