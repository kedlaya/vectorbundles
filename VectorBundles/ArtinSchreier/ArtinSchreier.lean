module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Ring.Semireal.Defs

@[expose] public section

lemma Field.RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosed K]
  (h : Module.rank F K = 2)
  (h1 : Irreducible (Polynomial.X ^ 2 + Polynomial.C 1)) :
  IsRealClosed F := by
  refine
    { toIsSemireal := ?_, isSquare_or_isSquare_neg := ?_, exists_isRoot_of_odd_natDegree := ?_ }
  -- IsSemireal F
  refine IsSemireal.of_not_isSumSq_neg_one ?_
  sorry
  -- ∀ (x : F), IsSquare x ∨ IsSquare (-x)
  sorry
  -- ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x
  sorry


theorem Field.artin_schreier_thm (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsAlgClosed K] : IsAlgClosed F ∨ IsRealClosed F := by
  sorry
