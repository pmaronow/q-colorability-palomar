module

public import ThLean.BP.S6.Potential

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations

namespace ThLean.W.S631

private theorem edge_nonempty (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (ThLean.BP.S6.Edge n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [a, b] at hv
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  have hpair := (Sym2.eq_iff).mp hv
  rcases hpair with ⟨hav, hbv⟩ | ⟨hav, hbv⟩
  · exact hab (hav.trans hbv.symm)
  · exact hab (hav.trans hbv.symm)

private theorem degree_tupleGraph_sum (n m : ℕ) (x : ThLean.BP.S6.Hist n m)
    (u : Fin n)
    [DecidablePred (fun e : Sym2 (Fin n) => Touches u e)]
    [DecidablePred (fun i : Fin m => Touches u (x i).val)] :
    degree (tupleGraph x) u =
      ∑ i : Fin m, if Touches u (x i).val then 1 else 0 := by
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  simp only [degree, tupleGraph]
  simp_rw [Finset.card_filter]
  have hsum :
      (∑ e : Sym2 (Fin n), if Touches u e then
        ∑ i : Fin m, if (x i).val = e then 1 else 0 else 0) =
      ∑ e : Sym2 (Fin n), ∑ i : Fin m,
        if Touches u e ∧ (x i).val = e then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    by_cases ht : Touches u e <;> simp [ht]
  calc
    (∑ e : Sym2 (Fin n), if Touches u e then
        ∑ i : Fin m, if (x i).val = e then 1 else 0 else 0) =
        ∑ e : Sym2 (Fin n), ∑ i : Fin m,
          if Touches u e ∧ (x i).val = e then 1 else 0 := hsum
    _ = ∑ i : Fin m, ∑ e : Sym2 (Fin n),
          if Touches u e ∧ (x i).val = e then 1 else 0 := Finset.sum_comm
    _ = ∑ i : Fin m, if Touches u (x i).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ht : Touches u (x i).val
      · have hsumCard :
            (∑ e : Sym2 (Fin n),
              if Touches u e ∧ (x i).val = e then 1 else 0) =
              (Finset.univ.filter (fun e : Sym2 (Fin n) =>
                Touches u e ∧ (x i).val = e)).card := by
          symm
          rw [Finset.card_filter]
        rw [hsumCard]
        have hset :
            Finset.univ.filter (fun e : Sym2 (Fin n) =>
              Touches u e ∧ (x i).val = e) = {(x i).val} := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · rintro ⟨_, he⟩
            exact he.symm
          · intro he
            rw [he]
            exact ⟨ht, rfl⟩
        rw [hset]
        simp [ht]
      · have hsumCard :
            (∑ e : Sym2 (Fin n),
              if Touches u e ∧ (x i).val = e then 1 else 0) =
              (Finset.univ.filter (fun e : Sym2 (Fin n) =>
                Touches u e ∧ (x i).val = e)).card := by
          symm
          rw [Finset.card_filter]
        rw [hsumCard]
        have hset :
            Finset.univ.filter (fun e : Sym2 (Fin n) =>
              Touches u e ∧ (x i).val = e) = ∅ := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty]
          constructor
          · rintro ⟨he, hxe⟩
            rw [← hxe] at he
            exact ht he
          · intro he
            exact False.elim he
        rw [hset]
        simp [ht]

private theorem uniformMean_not (A : Type) [Fintype A] (P : A → Prop)
    (hA : 0 < Fintype.card A) :
    uniformMean (fun a => indicator (¬ P a)) = 1 - uniformProb P := by
  have hsum :
      (∑ a : A, indicator (¬ P a)) =
        (Fintype.card A : ℝ) - ∑ a : A, indicator (P a) := by
    calc
      (∑ a : A, indicator (¬ P a)) =
          ∑ a : A, (1 - indicator (P a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : P a <;> simp [indicator, h]
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  change (∑ a : A, indicator (¬ P a)) / (Fintype.card A : ℝ) =
    1 - (∑ a : A, indicator (P a)) / (Fintype.card A : ℝ)
  rw [hsum]
  field_simp [hcard]

private theorem degree_append (n m : ℕ) (x : ThLean.BP.S6.Hist n (m + 1))
    (u : Fin n)
    [DecidablePred (fun e : Sym2 (Fin n) => Touches u e)] :
    degree (tupleGraph x) u =
      degree (tupleGraph (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)) u +
        (if Touches u (x ⟨m, Nat.lt_succ_self m⟩).val then 1 else 0) := by
  classical
  letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  letI : DecidablePred (fun e : Sym2 (Fin n) => Touches u e) :=
    fun e => Classical.propDecidable _
  letI : DecidablePred (fun i : Fin (m + 1) => Touches u (x i).val) :=
    fun i => Classical.propDecidable _
  letI : DecidablePred (fun i : Fin m =>
      Touches u (ThLean.BP.S6.takePrefix (Nat.le_succ m) x i).val) :=
    fun i => Classical.propDecidable _
  rw [degree_tupleGraph_sum, degree_tupleGraph_sum]
  rw [Fin.sum_univ_castSucc]
  have hlast : (Fin.last m : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ := by
    apply Fin.ext
    rfl
  rw [hlast]
  congr 1 <;> simp [ThLean.BP.S6.takePrefix]

private theorem uniformMean_add (A : Type) [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  unfold uniformMean
  rw [Finset.sum_add_distrib]
  ring

private theorem uniformMean_mul_const (A : Type) [Fintype A] (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  unfold uniformMean
  rw [← Finset.sum_mul]
  ring

set_option maxHeartbeats 500000 in
private theorem degree_probability_succ
    (h01b : ThLean.BP.S6.S6_01bStatement)
    (h03 : ThLean.BP.S6.S6_03Statement)
    (n m k : ℕ) (hn : 3 ≤ n) (u : Fin n) :
    uniformProb (fun x : ThLean.BP.S6.Hist n (m + 1) =>
      degree (tupleGraph x) u = k) =
    (1 - 2 / (n : ℝ)) *
        uniformProb (fun x : ThLean.BP.S6.Hist n m => degree (tupleGraph x) u = k) +
      (2 / (n : ℝ)) *
        (if k = 0 then 0 else
          uniformProb (fun x : ThLean.BP.S6.Hist n m => degree (tupleGraph x) u = k - 1)) := by
  letI : Nonempty (ThLean.BP.S6.Edge n) := edge_nonempty n hn
  letI : DecidablePred (fun e : Sym2 (Fin n) => Touches u e) :=
    fun e => Classical.propDecidable _
  let p : ℝ := 2 / (n : ℝ)
  let J : ThLean.BP.S6.Hist n m → ℝ := fun x =>
    indicator (degree (tupleGraph x) u = k)
  let K : ThLean.BP.S6.Hist n m → ℝ := fun x =>
    if k = 0 then 0 else indicator (degree (tupleGraph x) u = k - 1)
  let Z : ThLean.BP.S6.Hist n m → ThLean.BP.S6.Edge n → ℝ := fun _ e =>
    indicator (Touches u e.val)
  let Zc : ThLean.BP.S6.Hist n m → ThLean.BP.S6.Edge n → ℝ := fun _ e =>
    indicator (¬ Touches u e.val)
  have hpProb : uniformProb (fun e : ThLean.BP.S6.Edge n => Touches u e.val) = p := by
    simpa [p] using (h03 n hn).2.2 u
  have hp : uniformMean (fun e : ThLean.BP.S6.Edge n => indicator (Touches u e.val)) = p := by
    simpa [uniformProb] using hpProb
  have hEdge : 0 < Fintype.card (ThLean.BP.S6.Edge n) :=
    Fintype.card_pos_iff.mpr ‹Nonempty (ThLean.BP.S6.Edge n)›
  have hpc0 := uniformMean_not (ThLean.BP.S6.Edge n)
    (fun e => Touches u e.val) hEdge
  rw [hpProb] at hpc0
  have hpc : uniformMean (fun e : ThLean.BP.S6.Edge n => indicator (¬ Touches u e.val)) = 1 - p := by
    simpa using hpc0
  have hsplit : ∀ x : ThLean.BP.S6.Hist n (m + 1),
      indicator (degree (tupleGraph x) u = k) =
        J (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
            Zc (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
              (x ⟨m, Nat.lt_succ_self m⟩) +
          K (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
            Z (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
              (x ⟨m, Nat.lt_succ_self m⟩) := by
    intro x
    rw [degree_append]
    by_cases ht : Touches u (x ⟨m, Nat.lt_succ_self m⟩).val
    · by_cases hk : k = 0
      · simp [J, K, Z, Zc, indicator, ht, hk]
      · have hEq :
          (degree (tupleGraph (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)) u + 1 = k) ↔
            degree (tupleGraph (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)) u = k - 1 := by omega
        simp [J, K, Z, Zc, indicator, ht, hk, hEq]
    · simp [J, K, Z, Zc, indicator, ht]
  have hZ : ∀ x : ThLean.BP.S6.Hist n m, uniformMean (Z x) = p := by
    intro x
    simpa [Z] using hp
  have hZc : ∀ x : ThLean.BP.S6.Hist n m, uniformMean (Zc x) = 1 - p := by
    intro x
    simpa [Zc] using hpc
  change uniformMean (fun x : ThLean.BP.S6.Hist n (m + 1) =>
      indicator (degree (tupleGraph x) u = k)) =
    (1 - p) * uniformMean (fun x : ThLean.BP.S6.Hist n m =>
      indicator (degree (tupleGraph x) u = k)) +
      p * (if k = 0 then 0 else uniformMean (fun x : ThLean.BP.S6.Hist n m =>
        indicator (degree (tupleGraph x) u = k - 1)))
  calc
    uniformMean (fun x : ThLean.BP.S6.Hist n (m + 1) => indicator (degree (tupleGraph x) u = k)) =
        uniformMean (fun x : ThLean.BP.S6.Hist n (m + 1) =>
          J (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
              Zc (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
                (x ⟨m, Nat.lt_succ_self m⟩) +
            K (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
              Z (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
                (x ⟨m, Nat.lt_succ_self m⟩)) := by
          apply congrArg uniformMean
          funext x
          exact hsplit x
    _ = uniformMean (fun x : ThLean.BP.S6.Hist n (m + 1) =>
          J (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
              Zc (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
                (x ⟨m, Nat.lt_succ_self m⟩)) +
        uniformMean (fun x : ThLean.BP.S6.Hist n (m + 1) =>
          K (ThLean.BP.S6.takePrefix (Nat.le_succ m) x) *
              Z (ThLean.BP.S6.takePrefix (Nat.le_succ m) x)
                (x ⟨m, Nat.lt_succ_self m⟩)) := by
          exact uniformMean_add _ _ _
    _ = uniformMean (fun x : ThLean.BP.S6.Hist n m => J x * uniformMean (Zc x)) +
        uniformMean (fun x : ThLean.BP.S6.Hist n m => K x * uniformMean (Z x)) := by
          rw [(h01b n hn).2 m J Zc, (h01b n hn).2 m K Z]
    _ = (1 - p) * uniformMean J + p * uniformMean K := by
          simp_rw [hZc, hZ]
          rw [uniformMean_mul_const, uniformMean_mul_const]
          ring
    _ = (1 - p) * uniformMean (fun x : ThLean.BP.S6.Hist n m =>
          indicator (degree (tupleGraph x) u = k)) +
        p * (if k = 0 then 0 else uniformMean (fun x : ThLean.BP.S6.Hist n m =>
          indicator (degree (tupleGraph x) u = k - 1))) := by
          by_cases hk : k = 0 <;> simp [J, K, hk, uniformMean]

private theorem binomialWeight_succ (m k : ℕ) (p : ℝ) :
    binomialWeight (m + 1) p k =
      (1 - p) * binomialWeight m p k +
        p * (if k = 0 then 0 else binomialWeight m p (k - 1)) := by
  cases k with
  | zero =>
      simp [binomialWeight, pow_succ]
      <;> ring
  | succ j =>
      by_cases hj : j + 1 ≤ m
      · have hjm : j ≤ m := by omega
        have hchoose : (m + 1).choose (j + 1) = m.choose j + m.choose (j + 1) :=
          Nat.choose_succ_succ m j
        have hpow : (m + 1) - (j + 1) = m - (j + 1) + 1 := by omega
        have hpow2 : m - j = m - (j + 1) + 1 := by omega
        have hk : j + 1 ≤ m + 1 := by omega
        simp [binomialWeight, hk, hj, hjm, Nat.succ_ne_zero,
          Nat.succ_sub_one, hchoose, hpow, hpow2, pow_succ]
        <;> ring
      · by_cases hjm : j ≤ m
        · have hjEq : j = m := by omega
          subst j
          simp [binomialWeight, pow_succ]
          <;> ring
        · have hjgt : m < j := by omega
          have hkm : ¬ j + 1 ≤ m := by omega
          have hkm1 : ¬ j + 1 ≤ m + 1 := by omega
          have hjm' : ¬ j ≤ m := by omega
          simp [binomialWeight, hkm, hkm1, hjm']

set_option maxHeartbeats 500000 in
private theorem degree_probability (h01b : ThLean.BP.S6.S6_01bStatement)
    (h03 : ThLean.BP.S6.S6_03Statement)
    (n m : ℕ) (hn : 3 ≤ n) (u : Fin n) :
    ∀ k : ℕ,
      uniformProb (fun x : ThLean.BP.S6.Hist n m => degree (tupleGraph x) u = k) =
        binomialWeight m (2 / (n : ℝ)) k := by
  induction m with
  | zero =>
      intro k
      classical
      have hdegree : ∀ x : ThLean.BP.S6.Hist n 0, degree (tupleGraph x) u = 0 := by
        intro x
        simp [degree, tupleGraph]
      by_cases hk : k = 0
      · subst k
        simp [uniformProb, uniformMean, hdegree, binomialWeight, indicator]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        simp [uniformProb, uniformMean, hdegree, binomialWeight, indicator,
          Nat.choose_eq_zero_of_lt hkpos]
        <;> omega
  | succ m ih =>
      intro k
      calc
        uniformProb (fun x : ThLean.BP.S6.Hist n (m + 1) => degree (tupleGraph x) u = k) =
            (1 - 2 / (n : ℝ)) *
                uniformProb (fun x : ThLean.BP.S6.Hist n m => degree (tupleGraph x) u = k) +
              (2 / (n : ℝ)) *
                (if k = 0 then 0 else
                  uniformProb (fun x : ThLean.BP.S6.Hist n m => degree (tupleGraph x) u = k - 1)) :=
                  degree_probability_succ h01b h03 n m k hn u
        _ = (1 - 2 / (n : ℝ)) * binomialWeight m (2 / (n : ℝ)) k +
              (2 / (n : ℝ)) *
                (if k = 0 then 0 else binomialWeight m (2 / (n : ℝ)) (k - 1)) := by
              rw [ih k]
              by_cases hk : k = 0
              · simp [hk]
              · rw [ih (k - 1)]
        _ = binomialWeight (m + 1) (2 / (n : ℝ)) k := by
              symm
              exact binomialWeight_succ m k (2 / (n : ℝ))

theorem S6_30aStatement_of_deps
    (h01b : ThLean.BP.S6.S6_01bStatement)
    (h03 : ThLean.BP.S6.S6_03Statement) :
    ThLean.BP.S6.S6_30aStatement := by
  intro n m k hn u
  simpa [ThLean.BP.S6.binomialMass] using degree_probability h01b h03 n m hn u k

example (h01b : ThLean.BP.S6.S6_01bStatement)
    (h03 : ThLean.BP.S6.S6_03Statement) :
    ThLean.BP.S6.S6_30aStatement := S6_30aStatement_of_deps h01b h03

end ThLean.W.S631
