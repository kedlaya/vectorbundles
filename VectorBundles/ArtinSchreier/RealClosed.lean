module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Relrank

public import VectorBundles.ArtinSchreier.Polynomials
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField
open Module
open Polynomial

lemma RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
    (h1 : ∀ i : F, i^2 ≠ -1) (h2 : ∃ i : K, i^2 = -1 ∧ F⟮i⟯ = ⊤)
      : IsRealClosed F := by

  have h_alg : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  obtain ⟨i, h2a, h2b⟩ := h2
  have h_int : IsIntegral F i := Algebra.IsIntegral.isIntegral i
  let i_pol := minpoly F i
  let iota := algebraMap F K

  let pol := X ^ 2 + C (1 : F)
  have h_poldeg : pol.natDegree = 2 := natDegree_X_pow_add_C
  have h_pol : i_pol = pol := by
    have h_eval : aeval i pol = 0 := by
      calc
        aeval i pol = aeval i ((X : Polynomial F) ^ 2) + aeval i (C (1 : F)) := aeval_add i
        _ = i^2 + aeval i (C (1 : F)) := (add_left_inj ((aeval i) (C 1))).mpr (aeval_X_pow i)
        _ = i^2 + 1 := by
          refine (add_right_inj (i^2)).mpr ?_
          unfold aeval
          unfold aevalEquiv
          simp
        _ = 0 := add_eq_zero_iff_eq_neg.mpr h2a
    have h_div : i_pol ∣ pol := minpoly.dvd_iff.mpr h_eval
    have h_mon : pol.Monic := by
      refine monic_X_pow_add_C 1 ?_
      simp
    have _ : i_pol.natDegree = 2 := by
      have _ : i_pol.natDegree ≤ 2 := by
        have h_leq : i_pol.natDegree ≤ pol.natDegree := by
          apply natDegree_le_of_dvd h_div
          exact Monic.ne_zero h_mon
        simp
        exact le_of_le_of_eq h_leq h_poldeg
      have h_deg0 : 0 < i_pol.natDegree := minpoly.natDegree_pos h_int
      have h_degs : i_pol.natDegree = i_pol.degree :=
        ((fun hn => (degree_eq_iff_natDegree_eq_of_pos hn).mpr) h_deg0 rfl).symm
      have _ : i_pol.natDegree ≠ 1 := by
        by_contra
        have hi : i ∈ iota.range := by
          have h_deg : i_pol.degree = 1 := by
            simp_all
          apply minpoly.mem_range_of_degree_eq_one
          exact h_deg
        have hj : ∃ j : F, iota j = i := Set.mem_range.mp hi
        obtain ⟨j, hj⟩ := hj
        have _ : j^2 = -1 := by
          have _ : iota j ^ 2 = iota (-1) := by grind
          have _ : Function.Injective iota := FaithfulSMul.algebraMap_injective F K
          grind
        simp_all
      grind
    apply monic_divisor_of_same_degree i_pol pol
    · exact minpoly.monic h_int
    · exact h_mon
    · exact h_div
    · simp_all

  have h_rank2 : finrank F K = 2 := by
    have h_rel : relfinrank ⊥ F⟮i⟯ = 2 := by
      calc
        relfinrank ⊥ F⟮i⟯ = finrank F F⟮i⟯ := relfinrank_bot_left F⟮i⟯
        _ = (minpoly F i).natDegree := adjoin.finrank h_int
        _ = pol.natDegree := natDegree_eq_of_degree_eq (congrArg degree h_pol)
        _ = 2 := h_poldeg
    calc
      finrank F K = finrank (⊥: IntermediateField F K) K := finrank_bot'.symm
      _ = relfinrank ⊥ F⟮i⟯ * finrank F⟮i⟯ K :=
        have h_bot : ⊥ ≤ F⟮i⟯ := OrderBot.bot_le F⟮i⟯
        (IntermediateField.relfinrank_mul_finrank_top h_bot).symm
      _ = 2 * finrank F⟮i⟯ K := by
        rw [h_rel]
      _ = 2 * 1 := by
        have h_rank_to_top : finrank F⟮i⟯ K = 1 :=
          IntermediateField.finrank_eq_one_iff_eq_top.mpr h2b
        rw [h_rank_to_top]
      _ = 2 := by simp

  have issquare: ∀ (x : F), IsSquare x ∨ IsSquare (-x) :=
    quadratic_algebraic_closure_no_i F K h_rank2

  have h2 : ¬ IsSquare (-1 : F) := by
    by_contra
    unfold IsSquare at this
    obtain ⟨r, this⟩ := this
    specialize h1 r
    grind

  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    have h_ftog : ∀ f : Polynomial F, Irreducible f → f.natDegree ≤ 2 := by
      intro f h_irr
      have hy : ∃ y : K, aeval y f = 0 := by
        refine IsAlgClosed.exists_aeval_eq_zero K f ?_
        have _ : 0 < degree f := Irreducible.degree_pos h_irr
        aesop
      obtain ⟨y, hy⟩ := hy
      let g := minpoly F y
      have hdiv : g ∣ f := minpoly.dvd_iff.mpr hy
      have _ : g.natDegree = 0 ∨ g.natDegree = f.natDegree :=
        divisor_of_irreducible_poly g f hdiv h_irr
      have h_int : IsIntegral F y := Algebra.IsIntegral.isIntegral y
      have _ : g.natDegree ≤ 2 := by
        calc
        g.natDegree ≤ finrank F K := minpoly.natDegree_le y
        _ = 2 := h_rank2
      have _ : 0 < g.natDegree := minpoly.natDegree_pos h_int
      grind
    intro f h_odd
    have hg : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree :=
      odd_irreducible_factor f h_odd
    obtain ⟨g, hg, h_div, h_oddg⟩ := hg
    have h_x : ∃ x : F, g.IsRoot x := by
      refine exists_root_of_degree_eq_one ?_
      have h_natgdeg : g.natDegree = 1 := by
        have _ : g.natDegree ≤ 2 := h_ftog g hg
        grind
      calc
        g.degree = g.natDegree := by
          refine degree_eq_natDegree ?_
          exact Irreducible.ne_zero hg
        _ = 1 := Nat.cast_eq_one.mpr h_natgdeg
    obtain ⟨x, h_x⟩ := h_x
    use x
    exact IsRoot.dvd h_x h_div

  have semi: IsSemireal F := by
    have hs: ∀ x : F, ∀ y : F, ∃ z : F, x^2 + y^2 = z^2 := by
      intro x y
      have hssq : IsSquare (x ^ 2 + y^2) ∨ IsSquare (-y^2) :=
        quadratic_algebraic_closure F K h_rank2 x (y^2)
      cases hssq
      · rename_i hssq
        unfold IsSquare at hssq
        obtain ⟨z, hssq⟩ := hssq
        use z
        grind
      · rename_i hssq
        by_cases y = 0
        · use x
          grind
        · unfold IsSquare at hssq
          obtain ⟨r, hssq⟩ := hssq
          specialize h1 (r/y)
          grind
    have hssq: ∀ x : F, IsSumSq x → IsSquare x := by
      intro x hx
      induction hx with
      | zero =>
        unfold IsSquare
        use 0
        simp
      | sq_add y _ hz =>
          rcases hz with ⟨z, hz⟩
          unfold IsSquare
          subst hz
          obtain ⟨r, hr⟩ := hs y z
          use r
          ring_nf
          exact hr
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    have h2 : IsSquare (-1 : F) := hssq (-1) this
    grind

  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare,
       exists_isRoot_of_odd_natDegree := odd_deg }
