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
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Relrank
public import Mathlib.GroupTheory.Perm.Cycle.Type

public import VectorBundles.ArtinSchreier.ArtinSchreier

@[expose] public section

lemma quadratic_algebraic_closure_no_i (F : Type) (K : Type)
  [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsAlgClosure F K]
  (h : Module.finrank F K = 2) :
  ∀ (a : F), IsSquare a ∨ IsSquare (-a) := by
  have _: IsAlgClosed K := by
    exact IsAlgClosure.isAlgClosed F
  intro a
  let iota := algebraMap F K
  by_cases a = 0
  · left
    unfold IsSquare
    use 0
    simp_all
  have hi: ∃ i : K, i^2 = -1 := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp
  obtain ⟨i, hi⟩ := hi
  have hb : ∃ b : K, b^4 = iota a := by
    apply IsAlgClosed.exists_pow_nat_eq
    simp
  obtain ⟨b, hb⟩ := hb
  have hint : IsIntegral F b := by
    exact Algebra.IsIntegral.isIntegral b
  let f := minpoly F b
  let d := Polynomial.natDegree f
  have hd : d = 1 ∨ d = 2 := by
    have hf : d ≤ 2 := by
      grind [minpoly.natDegree_le]
    have _ : 0 < d := by
      exact minpoly.natDegree_pos hint
    grind
  have haeval : Polynomial.aeval b f = 0 := by
    exact minpoly.aeval F b
  have hc : ∃ c : F, (iota c)^4 = b^8 := by
    cases hd
    · have _ : (minpoly F b).natDegree = 1 := by
        (expose_names;
          exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm h_3)))))
      have _ : (minpoly F b).natDegree = 1 ↔ b ∈ iota.range := by
        exact minpoly.natDegree_eq_one_iff
      have _ : b ∈ iota.range := by
        (expose_names; exact minpoly.natDegree_eq_one_iff.mp h_3)
      have hb₀ : ∃ b₀ : F, iota b₀ = b := by
        (expose_names; exact Set.mem_range.mp h_6)
      obtain ⟨b₀, hb₀⟩ := hb₀
      use b₀^2
      grind

    · let g := Polynomial.X^4 - Polynomial.C a
      have _ : Polynomial.aeval b g = 0 := by
        unfold Polynomial.aeval
        subst g
        unfold Polynomial.aevalEquiv
        simp
        exact sub_eq_zero.mpr hb
      have hdiv : f ∣ g := by
        (expose_names; exact minpoly.dvd_iff.mpr h_4)
      let f_K := Polynomial.map (algebraMap F K) f
      let g_K := Polynomial.map (algebraMap F K) g
      have hdiv_K : f_K ∣ g_K := by
        exact Polynomial.map_dvd (algebraMap F K) hdiv
      have _ : f_K.roots ≤ g_K.roots := by
        apply Polynomial.roots.le_of_dvd
        refine (Polynomial.map_ne_zero_iff ?_).mpr ?_
        exact FaithfulSMul.algebraMap_injective F K
        refine Polynomial.X_pow_sub_C_ne_zero ?_ a
        exact Nat.zero_lt_succ 3
        exact hdiv_K
      have _ : g_K.Splits := by
        exact IsAlgClosed.splits g_K
      have h_bnon : b ≠ 0 := by
        have _ : iota a ≠ 0 := by
          (expose_names; exact (map_ne_zero iota).mpr h_2)
        have _ : b^4 ≠ 0 := by
          (expose_names; exact Ne.symm (Ne.trans_eq (id (Ne.symm h_7)) (id (Eq.symm hb))))
        grind
      have h_rootsf : ∀ (x : K), x ∈ f_K.roots → (x/b)^4 = 1 := by
        intro x hx
        have hx1: x ∈ g_K.roots := by
          (expose_names; exact Multiset.mem_of_le h_5 hx)
        have hx2 : Polynomial.eval x g_K = 0 := by
          unfold Polynomial.roots at hx1
          refine Polynomial.IsRoot.def.mp ?_
          exact Polynomial.isRoot_of_mem_roots hx1
        have hxb : x^4 = b^4 := by
          have h_eval_aeval : Polynomial.eval x (Polynomial.map (algebraMap F K) g) = Polynomial.aeval x g :=
            Polynomial.eval_map_algebraMap g x
          have _ : (Polynomial.aeval x) g = 0 := by
            exact
              (AddSemiconjBy.eq_zero_iff (Polynomial.eval x (Polynomial.map (algebraMap F K) g))
                    (congrFun (congrArg HAdd.hAdd h_eval_aeval)
                      (Polynomial.eval x (Polynomial.map (algebraMap F K) g)))).mp
                hx2
          subst g
          have _ : 0 = (Polynomial.aeval x) (Polynomial.X ^ 4 - Polynomial.C a)  := by
            grind
          have _ : (Polynomial.aeval x) ((Polynomial.X : Polynomial F) ^ 4) = x^4 := by
            exact Polynomial.aeval_X_pow x
          have _ : (Polynomial.aeval x) (Polynomial.C a) = (algebraMap F K) a := by
            exact Polynomial.aeval_C x a
          grind
        have hxb2 : x^4/b^4 = b^4/b^4 := by
          exact (div_eq_div_iff_comm (b ^ 4) (x ^ 4) (b ^ 4)).mp (congrArg (HDiv.hDiv (b ^ 4)) hxb)
        let y := x/b
        have _ : y^4 = 1 := by
         calc
          y^4 = x^4/b^4 := by exact div_pow x b 4
          _ = b^4/b^4 := by apply hxb2
          _ = 1 := by
            refine (div_eq_one_iff_eq ?_).mpr rfl
            exact pow_ne_zero 4 h_bnon
        (expose_names;
          exact (MulOpposite.op_eq_one_iff ((x / b) ^ 4)).mp (congrArg MulOpposite.op h_7))
      have hspl : f_K.Splits := by
        exact Normal.splits' b
      have hmon : f_K.Monic := by
        refine Polynomial.Monic.map (algebraMap F K) ?_
        exact minpoly.monic hint
      let lin := Polynomial.X - Polynomial.C b
      let res := f_K /ₘ lin
      have _ : res * lin = f_K := by
        have _ : f_K %ₘ lin + lin * (f_K /ₘ lin) = f_K :=
          Polynomial.modByMonic_add_div f_K lin
        have _ : Polynomial.aeval b (minpoly F b) = 0 :=
          minpoly.aeval F b
        have _ : Polynomial.IsRoot f_K b := by
          refine Polynomial.IsRoot.def.mpr ?_
          have _ : Polynomial.aeval b f_K = Polynomial.aeval b f := by
            exact Polynomial.aeval_map_algebraMap K b f
          (expose_names;
            exact
              (AddSemiconjBy.eq_zero_iff ((Polynomial.aeval b) f)
                    (congrFun (congrArg HAdd.hAdd (id (Eq.symm h_9))) ((Polynomial.aeval b) f))).mp
                haeval)
        have hdiv_res : lin ∣ f_K := by
          refine Polynomial.dvd_iff_isRoot.mpr ?_
          refine Polynomial.IsRoot.def.mpr ?_
          (expose_names; exact Polynomial.IsRoot.def.mp h_9)
        have hdiv_mod : f_K %ₘ lin = 0 ↔ lin ∣ f_K := by
          apply Polynomial.modByMonic_eq_zero_iff_dvd
          exact Polynomial.monic_X_sub_C b
        grind
      have _ : lin.leadingCoeff = 1 := by
        exact Polynomial.leadingCoeff_X_sub_C b
      have _ : res.natDegree = 1 := by
        have h_lead : res.leadingCoeff * lin.leadingCoeff ≠ 0 := by
          simp
          by_contra
          have _ : f_K = 0 := by grind
          have _ : f_K ≠ 0 := by exact Polynomial.Monic.ne_zero hmon
          simp_all
        have _ : (res * lin).natDegree = res.natDegree + lin.natDegree :=
          Polynomial.natDegree_mul' h_lead
        have _ : lin.natDegree = 1 := by
          exact Polynomial.natDegree_X_sub_C b
        have _ : f_K.natDegree = f.natDegree := by
          exact Polynomial.natDegree_map (algebraMap F K)
        have h_fdeg2 : f.natDegree = 2 := by
          (expose_names;
            exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm h_3)))))
        simp_all
      have h_resmonic : res.Monic := by
        refine Polynomial.Monic.def.mpr ?_
        have h_mon1 : lin.Monic := by
          exact Polynomial.monic_X_sub_C b
        have _ : (res * lin).leadingCoeff = res.leadingCoeff :=
          Polynomial.leadingCoeff_mul_monic h_mon1
        have _: f_K.leadingCoeff = 1 := by
          exact Polynomial.Monic.def.mp hmon
        grind
      let z := -res.coeff 0
      have _ : res = Polynomial.X - Polynomial.C z := by
        refine Polynomial.ext ?_
        intro n
        by_cases n = 0
        simp_all
        grind
        by_cases n = 1
        simp_all
        have _ : res.coeff res.natDegree = 1 :=
          Polynomial.Monic.coeff_natDegree h_resmonic
        grind
        have _ : n > res.natDegree := by
          grind
        have _ : res.coeff n = 0 := by
          (expose_names; exact Polynomial.coeff_eq_zero_of_natDegree_lt h_12)
        have _ : (Polynomial.X : Polynomial K).coeff n = 0 := by
          (expose_names; exact Polynomial.coeff_X_of_ne_one h_11)
        simp_all
        (expose_names; exact Polynomial.coeff_C_ne_zero h_10)
      have _ : Polynomial.IsRoot f_K z := by
        have _ : Polynomial.eval z f_K = 0 := by
          have _ : Polynomial.eval z res = 0 := by
            have _ : Polynomial.eval z (Polynomial.X : Polynomial K) = z := by
              exact Polynomial.eval_X
            have _ : Polynomial.eval z (Polynomial.C z) = z := by
              exact Polynomial.eval_C
            have _ : Polynomial.eval z (Polynomial.X - Polynomial.C z) =
              Polynomial.eval z (Polynomial.X : Polynomial K) -
              Polynomial.eval z (Polynomial.C z) := by
                exact Polynomial.eval_sub Polynomial.X (Polynomial.C z) z
            simp_all
          have _ : Polynomial.eval z (res * lin) =
            Polynomial.eval z res * Polynomial.eval z lin := by
            exact Polynomial.eval_mul
          simp_all
        (expose_names; exact Polynomial.IsRoot.def.mpr h_11)
      have h_zroots : z ∈ f_K.roots := by
        have h_fK: f_K ≠ 0 := by exact Polynomial.Monic.ne_zero hmon
        have _ : z ∈ f_K.roots ↔ f_K.IsRoot z :=
          Polynomial.mem_roots h_fK
        simp
        constructor
        · exact Polynomial.Monic.ne_zero_of_polynomial_ne hmon h_fK
        · (expose_names; exact Polynomial.IsRoot.def.mp h_11)
      have _ : f_K.coeff 0 = z * b := by
        have h_coeff0 : (res * lin).coeff 0 = res.coeff 0 * lin.coeff 0 := by
          exact Polynomial.mul_coeff_zero res lin
        have _ : lin.coeff 0 = -b := by
          subst lin
          have _ : (Polynomial.X - Polynomial.C b).coeff 0 = (Polynomial.X : Polynomial K).coeff 0
            - (Polynomial.C b).coeff 0 := by
            exact Polynomial.coeff_sub Polynomial.X (Polynomial.C b) 0
          simp
        simp_all
      have h_c : ∃ c : F, iota c = b * z := by
        use f.coeff 0
        have _ : iota (f.coeff 0) = f_K.coeff 0 := by
          exact Eq.symm (Polynomial.coeff_map iota 0)
        simp_all
        exact Eq.symm (CommMonoid.mul_comm b z)
      obtain ⟨c, h_c⟩ := h_c
      use c
      have _ : (iota c)^2 = (b * z)^2 := by
        refine (Commute.sq_eq_sq_iff_eq_or_eq_neg ?_).mpr ?_
        exact Algebra.commute_algebraMap_left c (b * z)
        left
        exact h_c
      grind
  unfold IsSquare
  obtain ⟨c, hc⟩ := hc
  have hc1 : iota (c^4) = iota (a^2) := by
    grind
  have _ : c^4 = a^2 := by
    have _ : Function.Injective iota := by
      exact FaithfulSMul.algebraMap_injective F K
    grind
  have hc : c^2 = a ∨ c^2 = -a := by
    grind
  cases hc
  · left
    use c
    grind
  · right
    use c
    grind
