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
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

public import VectorBundles.ArtinSchreier.Polynomials
public import VectorBundles.ArtinSchreier.FieldTheory2
public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

open IntermediateField

lemma RealClosed_from_quadratic (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h1 : ∀ i : F, i^2 ≠ -1) (h2 : ∃ i : K, i^2 = -1 ∧ F⟮i⟯ = ⊤)
  : IsRealClosed F := by

  have h_alg : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  obtain ⟨i, h2a, h2b⟩ := h2
  have h_int : IsIntegral F i := Algebra.IsIntegral.isIntegral i
  let i_pol := minpoly F i
  let iota := algebraMap F K

  let pol := Polynomial.X ^ 2 + Polynomial.C (1 : F)
  have h_poldeg : pol.natDegree = 2 := by
    exact Polynomial.natDegree_X_pow_add_C
  have _ : i_pol = pol := by
    have h_eval : Polynomial.aeval i pol = 0 := by
      have _ : Polynomial.aeval i pol = Polynomial.aeval i ((Polynomial.X : Polynomial F) ^ 2) + Polynomial.aeval i (Polynomial.C (1 : F)) := by
        subst pol
        exact Polynomial.aeval_add i
      have _ : Polynomial.aeval i ((Polynomial.X : Polynomial F) ^ 2) = i^2 := by
        exact Polynomial.aeval_X_pow i
      have _ : Polynomial.aeval i (Polynomial.C (1 : F)) = 1 := by
        unfold Polynomial.aeval
        unfold Polynomial.aevalEquiv
        simp
      grind
    have h_div : i_pol ∣ pol := by
      subst pol
      exact minpoly.dvd_iff.mpr h_eval
    have h_mon : pol.Monic := by
      refine Polynomial.monic_X_pow_add_C 1 ?_
      simp
    have _ : i_pol.natDegree ≤ 2 := by
      have h_leq : i_pol.natDegree ≤ pol.natDegree := by
        apply Polynomial.natDegree_le_of_dvd
        exact h_div
        exact Polynomial.Monic.ne_zero h_mon
      simp
      exact le_of_le_of_eq h_leq h_poldeg
    have _ : i_pol.natDegree > 0 := by
      subst i_pol
      have _ : IsIntegral F i → 0 < (minpoly F i).natDegree := by
        apply minpoly.natDegree_pos
      simp_all
    have _ : i_pol.natDegree ≠ 1 := by
      have _ : i_pol.natDegree = i_pol.degree := by
        (expose_names; exact Eq.symm ((fun hn => (Polynomial.degree_eq_iff_natDegree_eq_of_pos hn).mpr) h_1 rfl))
      by_contra
      have _ : i_pol.degree = 1 := by
        simp_all
      subst i_pol
      have _ : i ∈ iota.range := by
        apply minpoly.mem_range_of_degree_eq_one
        (expose_names;
          exact (MulOpposite.op_eq_one_iff (minpoly F i).degree).mp (congrArg MulOpposite.op h_3))
      have hj : ∃ j : F, iota j = i := by
        (expose_names; exact Set.mem_range.mp h_4)
      obtain ⟨j, hj⟩ := hj
      have _ : iota j ^ 2 = iota (-1) := by
        grind
      have _ : Function.Injective iota := by
        exact FaithfulSMul.algebraMap_injective F K
      have _ : j^2 = -1 := by
        grind
      simp_all
    have _ : i_pol.natDegree = 2 := by
      grind
    apply monic_divisor_of_same_degree i_pol pol
    subst i_pol
    apply minpoly.monic
    exact h_int
    exact h_mon
    exact h_div
    simp_all

  have h_rank2 : Module.finrank F K = 2 := by
    have h_fromdeg : Module.finrank F F⟮i⟯ = (minpoly F i).natDegree := by
      exact adjoin.finrank h_int
    have _ : Module.finrank F⟮i⟯ K = 1 ↔ F⟮i⟯ = (⊤: IntermediateField F K) :=
      IntermediateField.finrank_eq_one_iff_eq_top
    have h_rank_to_top : Module.finrank F⟮i⟯ K = 1 := by
      simp_all
    have h_relfinrank : Module.finrank F F⟮i⟯ = relfinrank ⊥ F⟮i⟯ :=
      Eq.symm (relfinrank_bot_left F⟮i⟯)
    have h_bot : ⊥ ≤ F⟮i⟯ := by
      exact OrderBot.bot_le F⟮i⟯
    have h_prod : relfinrank ⊥ F⟮i⟯ * Module.finrank F⟮i⟯ K = Module.finrank (⊥: IntermediateField F K) K :=
      IntermediateField.relfinrank_mul_finrank_top h_bot
    have h_bot_to_top :  Module.finrank (⊥: IntermediateField F K) K =  Module.finrank F K := by
      exact finrank_bot'
    have _ : relfinrank ⊥ F⟮i⟯ = 2 := by
      calc
      relfinrank ⊥ F⟮i⟯ = Module.finrank F F⟮i⟯ := by
        symm
        apply h_relfinrank
      _ = (minpoly F i).natDegree := by apply h_fromdeg
      _ = i_pol.natDegree := by
        subst i_pol
        simp
      _ = pol.natDegree := by
        (expose_names; exact Polynomial.natDegree_eq_of_degree_eq (congrArg Polynomial.degree h))
      _ = 2 := by exact h_poldeg
    calc
      Module.finrank F K = Module.finrank (⊥: IntermediateField F K) K := by
        symm
        apply h_bot_to_top
      _ = relfinrank ⊥ F⟮i⟯ * Module.finrank F⟮i⟯ K := by
        symm
        apply h_prod
      _ = 2 * Module.finrank F⟮i⟯ K := by
        (expose_names;
          exact
            Nat.succ_inj.mp
              (congrArg Nat.succ (congrFun (congrArg HMul.hMul h_2) (Module.finrank (↥F⟮i⟯) K))))
      _ = 2 * 1 := by
        exact Nat.succ_inj.mp (congrArg Nat.succ (congrArg (HMul.hMul 2) h_rank_to_top))
      _ = 2 := by simp

  have issquare: ∀ (x : F), IsSquare x ∨ IsSquare (-x) := by
    intro x
    apply quadratic_algebraic_closure_no_i F K
    apply h_rank2

  have h2 : ¬ IsSquare (-1 : F) := by
    by_contra
    unfold IsSquare at this
    obtain ⟨r, this ⟩ := this
    specialize h1 r
    grind

  have odd_deg : ∀ {f : Polynomial F}, Odd f.natDegree → ∃ x, f.IsRoot x := by
    have h_ftog : ∀ f : Polynomial F, Irreducible f → f.natDegree ≤ 2 := by
      intro f h_irr
      have hy : ∃ y : K, Polynomial.aeval y f = 0 := by
        refine IsAlgClosed.exists_aeval_eq_zero K f ?_
        have _ : Irreducible f → 0 < Polynomial.degree f :=
          Irreducible.degree_pos
        grind
      obtain ⟨y, hy⟩ := hy
      let g := minpoly F y
      have _ : Irreducible g := by
        refine minpoly.irreducible ?_
        exact Algebra.IsIntegral.isIntegral y
      have _ : g.natDegree ≤ 2 := by
        have _ : (minpoly F y).natDegree ≤ Module.finrank F K := by
          apply minpoly.natDegree_le
        subst g
        simp_all
      have _ : g.natDegree > 0 := by
        subst g
        have _ : IsIntegral F y → 0 < (minpoly F y).natDegree := by
          apply minpoly.natDegree_pos
        have _ : IsIntegral F y := by
          exact Algebra.IsIntegral.isIntegral y
        simp_all
      have hdiv : g ∣ f := by
        exact minpoly.dvd_iff.mpr hy
      have _ : g.natDegree = 0 ∨ g.natDegree = f.natDegree := by
        apply divisor_of_irreducible_poly g f hdiv h_irr
      grind
    intro f h_odd
    have hg : ∃ (g : Polynomial F), Irreducible g ∧ g ∣ f ∧ Odd g.natDegree := by
      apply odd_irreducible_factor f h_odd
    obtain ⟨g, hg, h_div, h_oddg⟩ := hg
    have _ : g.natDegree ≤ 2 := by
      apply h_ftog g hg
    have h_natgdeg : g.natDegree = 1 := by
      grind
    have h_gdeg : g.degree = g.natDegree := by
      refine Polynomial.degree_eq_natDegree ?_
      exact Irreducible.ne_zero hg
    have h_x : ∃ x : F, g.IsRoot x := by
      refine Polynomial.exists_root_of_degree_eq_one ?_
      calc
        g.degree = g.natDegree := h_gdeg
        _ = 1 := Nat.cast_eq_one.mpr h_natgdeg
    obtain ⟨x, h_x⟩ := h_x
    use x
    exact Polynomial.IsRoot.dvd h_x h_div

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
        · exfalso
          unfold IsSquare at hssq
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
          grind
    rw [isSemireal_iff_not_isSumSq_neg_one]
    by_contra
    have h2 : IsSquare (-1 : F) := by
      specialize hssq (-1)
      apply hssq
      apply this
    grind

  refine
    { toIsSemireal := semi, isSquare_or_isSquare_neg := issquare, exists_isRoot_of_odd_natDegree := odd_deg }
