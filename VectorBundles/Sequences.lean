module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Defs

@[expose] public section

lemma sequence_argument1 (n : ℕ) (m : ℕ → ℤ)
  (h0 : ¬ ∃ (i j : ℕ), i < j ∧ j < n ∧ m j > m i + 1 ∧
    ∀ (k : ℕ), i < k → k < j → m k = m i + 1)
      : ∀ (i j : ℕ), i < j → j < n → m j ≤ m i + 1 := by
  have h : ∀ d : ℕ, ∀ (i j : ℕ), j - i ≤ d + 1 → i < j → j < n → m j ≤ m i + 1 := by
    intro d
    induction d with
      | zero =>
        intro i j h3 h4 h5
        by_contra
        push Not at h0
        push Not at this
        specialize h0 i j h4 h5 this
        obtain ⟨k, h0⟩ := h0
        grind
      | succ d hyp =>
        intro i j
        by_cases j - i ≤ d + 1
        · intro h1 h2 h3
          grind
        · intro h4
          have _ : j - i = d + 2 := by
            grind
          by_contra
          push Not at this
          obtain ⟨h2, h3, h4⟩ := this
          let mid := m i + 1
          have h_mid : ∀ k : ℕ, i < k → k < j → m k = mid ∧ m j = mid + 1 := by
            intro k h5 h6
            have h_in1 : m k ≤ mid :=
              have h1' : k - i ≤ d + 1 := by grind
              have h3' : k < n := by calc
                k < j := h6
                _ < n := h3
              hyp i k h1' h5 h3'
            have h_in2 : m j ≤ m k + 1 :=
              have h1'' : j - k ≤ d + 1 := by grind
              hyp k j h1'' h6 h3
            have h4' : m i + 2 ≤ m j := by grind
            have : m i + 2 = m j := by grind
            grind
          have h_j : m j = mid + 1 := by
            have h_j1 : i < i + 1 := by grind
            have h_j2 : i + 1 < j := by grind
            specialize h_mid (i + 1) h_j1 h_j2
            obtain ⟨_, h_j3⟩ := h_mid
            apply h_j3
          have h_k : ∀ k : ℕ, i < k → k < j → m k = mid ∧ m j = mid + 1 := by
            grind
          grind
  intro i j h1 h2
  specialize h (j - i) i j
  grind

lemma sequence_argument2 (n: ℕ) (m : ℕ → ℤ) :
  ∀ c : ℤ, 0 ≤ c → c < n → (∑ a ∈ Finset.range n, m a = c) →
    (∀ i j: ℕ, i < j → j < n → m i ≤ m j) →
      (∀ (i j : ℕ), i < j → j < n → m j ≤ m i + 1) →
         (∀ i : ℕ, i < n → m i = if i < n-c then 0 else 1) := by
  induction n with
  | zero =>
    grind
  | succ n hyp =>
    intro c h h0 h1 h2 h3
    let c' := ∑ a ∈ Finset.range n, m a
    have h_split : c' + m n = c := by
      rw [← h1]
      exact (Finset.sum_range_succ m n).symm
    have hi2 : (n : ℤ) = ∑ a ∈ Finset.range n, 1 :=
      (Finset.sum_range_induction (fun k => 1) Nat.cast rfl n fun k => congrFun rfl).symm
    have : (m n - 1) * n ≤ c' := by
      have hi1 : ∀ i : ℕ, i < n → m n - 1 ≤ m i := by
        intro i hi
        specialize h3 i n hi (Nat.lt_succ_self n)
        grind
      calc
        (m n - 1) * n = (m n - 1) * (∑ a ∈ Finset.range n, ↑1) :=
          congrArg (fun a ↦ (m n - 1) * a) hi2
        _= ∑ a ∈ Finset.range n, ((m n - 1) * 1) := by
          apply Finset.mul_sum
        _ =  ∑ a ∈ Finset.range n, (m n - 1) := by simp
        _ ≤ c' := by
          apply Finset.sum_le_sum
          intro i hi
          apply hi1 i
          exact List.mem_range.mp hi
    have : c' ≤ m n * n := by
      have hi1 : ∀ i : ℕ, i < n → m i ≤ m n := by
        intro i hi
        exact h2 i n hi (Nat.lt_succ_self n)
      calc
        c' ≤ ∑ a ∈ Finset.range n, m n := by
          apply Finset.sum_le_sum
          intro i hi
          apply hi1 i
          exact List.mem_range.mp hi
        _ = ∑ a ∈ Finset.range n, (m n * 1) := by simp
        _ = (m n) * ∑ a ∈ Finset.range n, 1 := by
          symm
          apply Finset.mul_sum
        _ = m n * n :=
          congrArg (fun a ↦ m n * a) hi2.symm
    have : (n + 1) * m n - n ≤ c := by grind
    have : c ≤ (n + 1) * m n := by grind
    have hn1 : 0 < n + 1 := by grind
    have h_can : ∀ a : ℕ, ∀ (b c : ℤ), a > 0 → a * b < a * c → b < c :=
      fun a b c a_1 a_2 => lt_of_nsmul_lt_nsmul_right a a_2
    have h_top : m n = if n < n + 1 - c then 0 else 1 := by
      by_cases c = 0
      · have ha : m n < 1 := by
          have hn2 : (n + 1) * m n < (n + 1) * 1 := by grind
          exact h_can (n + 1) (m n) 1 hn1 hn2
        have hb : -1 < m n := by
          have hn2 : (n + 1) * -1 < (n + 1) * m n := by grind
          exact h_can (n + 1) (-1) (m n) hn1 hn2
        grind
      · have ha : m n < 2 := by
          have hn2 : (n + 1) * m n < (n + 1) * 2 := by grind
          exact h_can (n + 1) (m n) 2 hn1 hn2
        have hb : 0 < m n := by
          have hn2 : (n + 1) * 0 < (n + 1) * m n := by grind
          exact h_can (n + 1) 0 (m n) hn1 hn2
        grind
    grind

lemma partial_sums_of_monotone_sequence (n : ℕ) (m : ℕ → ℤ)
  (h : ∀ (i j : ℕ), i < j → j < n → m i ≤ m j) :
    ∀ i : ℕ, i < n → ∑ a ∈ Finset.range i, m a
      ≤ i * (∑ a ∈ Finset.range n, m a) / n := by
  intro i
  induction n with
  | zero =>

    sorry
  | succ hyp =>
    intro hi
    sorry

lemma sequence_argument4 (n: ℕ) (c: ℤ) (h0: 0 ≤ c ∧ c < n) (S : Set (ℕ → ℤ))
  (h1 : S.Nonempty) (h2 : ∀ (m : ℕ → ℤ), m ∈ S → ∑ a ∈ Finset.range n, m a = c)
    (h3 : ∀ (m : ℕ → ℤ), m ∈ S → ∀ (i j : ℕ), i < j → j < n → m i ≤ m j)
      (h4: ∀ (m : ℕ → ℤ), m ∈ S → ∀ (i j : ℕ), i < j → j < n → m j > m i + 1 →
        (∀ (k : ℕ), i < k → k < j → m k = m i + 1) →
          ∃ (m' : ℕ → ℤ), m' ∈ S ∧ ∑ a ∈ Finset.range i, m a > ∑ a ∈ Finset.range i, m' a
            ∧ ∀ k : ℕ, k < n → k ≠ i → ∑ a ∈ Finset.range k, m a ≥ ∑ a ∈ Finset.range k, m' a) :
              ∃ (m : ℕ → ℤ), m ∈ S ∧ ∀ i : ℕ, i < n →
                m i = if i < n-c then 0 else 1 := by
  have hn0: 0 < n := by grind
  let f1 : ℕ → (ℕ → ℤ) → ℤ := fun (j : ℕ) ↦ fun (m : ℕ → ℤ) ↦
    ∑ i ∈ Finset.range j, m i
  have hbd1 : ∀ m : ℕ → ℤ, m ∈ S → ∀ j : ℕ, j ∈ Finset.range n → f1 j m ≤ j * c / n := by
    intro m hm j hj1
    rw [← h2 m hm]
    have hj : j < n := List.mem_range.mp hj1
    apply partial_sums_of_monotone_sequence n m (h3 m hm) j hj
  let f : (ℕ → ℤ) → ℤ := fun (m : ℕ → ℤ) ↦ ∑ i ∈ Finset.range n, f1 i m
  have hbd2 : ∀ m : ℕ → ℤ, m ∈ S → f m ≤ ∑ i ∈ Finset.range n, i * c / n := by
    intro m hm
    apply Finset.sum_le_sum (hbd1 m hm)
  have hm: ∃ (m: ℕ → ℤ), m ∈ S ∧ ∀ (m': ℕ → ℤ), m' ∈ S → f m ≥ f m' := by
    let T := S.image f
    have hT: T.Nonempty := Set.image_nonempty.mpr h1
    have : BddAbove T := by
      refine bddAbove_def.mpr ?_
      use ∑ i ∈ Finset.range n, i * c / n
      intro t ht
      have hm : ∃ m : ℕ → ℤ, m ∈ S ∧ f m = t := by
        exact (Set.mem_image f S t).mp ht
      obtain ⟨m, hm1, hm2⟩ := hm
      rw [← hm2]
      apply hbd2 m hm1
    sorry
  obtain ⟨m, hm1, hm2⟩ := hm
  use m
  constructor
  · exact hm1
  have h_end1 : ¬ ∃ (i j : ℕ), i < j ∧ j < n ∧ m j > m i + 1 ∧
    ∀ (k : ℕ), i < k → k < j → m k = m i + 1 := by
      by_contra
      obtain ⟨i, j, h01, h02, h03, h04⟩ := this
      specialize h4 m hm1 i j h01 h02 h03 h04
      obtain ⟨m', hm'1, hm'2, hm'3⟩ := h4
      have h : ∀ k ∈ Finset.range n, (if k = i then 1 else 0)
        ≤ (∑ j ∈ Finset.range n with j ≤ k, m' j) - (∑ j ∈ Finset.range n with j ≤ k, m j) := by
        intro k hk
        by_cases hk: k = i
        · sorry
        · have hm'4 : k < n := by grind
          specialize hm'3 k hm'4 hk

          sorry
      have : 1 ≤ f m' - f m := by
        calc
          1 = ∑ a ∈ Finset.range n, if a = i then 1 else 0 := by sorry
          _ ≤ ∑ a ∈ Finset.range n, ((∑ j ∈ Finset.range n with j ≤ a, m' j) -
          (∑ j ∈ Finset.range n with j ≤ a, m j)) := by
            apply Finset.sum_le_sum h
          _ = f m' - f m :=
            sorry
--              (Finset.sum_sub_distrib (fun x => ∑ j ∈ Finset.range n with j ≤ x, m' j) fun x =>
--                ∑ j ∈ Finset.range n with j ≤ x, m j)
      grind
  have h_end2 : ∀ (i j : ℕ), i < j → j < n → m j ≤ m i + 1 :=
    sequence_argument1 n m h_end1
  obtain ⟨h0a, h0b⟩ := h0
  exact sequence_argument2 n m c h0a h0b (h2 m hm1) (h3 m hm1) h_end2
