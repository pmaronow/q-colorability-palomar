import ThLean.BP.S3.Lifetime

noncomputable section
open scoped BigOperators ENNReal
namespace ThLean.W.S324
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable

universe u v

private lemma pair_nonempty_of_card_two (V : Type u) [Fintype V]
    (hV : 2 ≤ Fintype.card V) : Nonempty (Pair V) := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro w heq
  have heq' := Sym2.eq_iff.mp heq
  rcases heq' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (ha.trans hb.symm)
  · exact hab (ha.trans hb.symm)

private lemma relabel_add {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (π : V ≃ W) (G H : MGraph V) :
    relabel π (G + H) = relabel π G + relabel π H := by
  classical
  funext e
  change
    (∑ d, if Sym2.map π d = e then G d + H d else 0) =
      (∑ d, if Sym2.map π d = e then G d else 0) +
        (∑ d, if Sym2.map π d = e then H d else 0)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : Sym2.map π d = e <;> simp [h]

private lemma colorable_relabel {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (h01 : S3_01Statement.{u, v}) (q : ℕ) (hq : 2 ≤ q)
    (π : V ≃ W) (G : MGraph V) :
    Colorable q (relabel π G) ↔ Colorable q G := by
  have hrel := (h01 V W q hq).2.2.2.1
  constructor
  · rintro ⟨τ, hτ⟩
    let σ : V → Fin q := τ ∘ π
    have hσ : IsColoring q (relabel π G) (σ ∘ π.symm) := by
      have hcomp : (τ ∘ π) ∘ π.symm = τ := by
        funext w
        simp
      rw [hcomp]
      exact hτ
    exact ⟨σ, (hrel G π σ).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ ∘ π.symm, ?_⟩
    exact (hrel G π σ).mpr hσ

private lemma colorable_of_subgraph {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (h01 : S3_01Statement.{u, v}) (q : ℕ) (hq : 2 ≤ q)
    (G H : MGraph V) (hsub : subgraph G H) :
    Colorable q H → Colorable q G := by
  classical
  intro hcolor
  rcases hcolor with ⟨σ, hσ⟩
  have hsubset := (h01 V W q hq).2.1 G H hsub
  have hmem : σ ∈ colorings q H := by simp [colorings, hσ]
  have hmem' : σ ∈ colorings q G := hsubset hmem
  exact ⟨σ, (Finset.mem_filter.mp hmem').2⟩

private lemma survival_mono {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (h01 : S3_01Statement.{u, v}) (q : ℕ) (hq : 2 ≤ q)
    (G H : MGraph V) (hsub : subgraph G H) (k : ℕ) :
    survival q H k ≤ survival q G k := by
  unfold survival uniformProb uniformMean
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro x hx
    unfold indicator
    by_cases hh : Colorable q (H + tupleGraph x)
    · have hg := colorable_of_subgraph (V := V) (W := W) h01 q hq
        (G + tupleGraph x) (H + tupleGraph x) (by
        intro e
        exact Nat.add_le_add_right (hsub e) _) hh
      simp [hh, hg]
    · by_cases hg : Colorable q (G + tupleGraph x) <;> simp [hh, hg]
  · exact Nat.cast_nonneg _

private lemma tuplePrefix_eq_tupleGraph_restrictTuple {V : Type u} [Fintype V]
    {b k : ℕ} (hkb : k ≤ b) (x : EdgeTuple V b) :
    tuplePrefix x k = tupleGraph (restrictTuple hkb x) := by
  classical
  funext e
  change
    (Finset.univ.filter (fun i : Fin b => i.val < k ∧ (x i).val = e)).card =
      (Finset.univ.filter
        (fun j : Fin k => (x ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkb⟩).val = e)).card
  refine Finset.card_bij
    (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2.1⟩) ?_ ?_ ?_
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · simpa using hi'.2
  · intro i hi j hj hij
    apply Fin.ext
    simpa using congrArg Fin.val hij
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val, Nat.lt_of_lt_of_le j.isLt hkb⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · exact ⟨j.isLt, hj'⟩
    · apply Fin.ext
      rfl

private lemma uniformMean_finset_sum {A : Type u} [Fintype A]
    {ι : Type v} (J : Finset ι) (f : ι → A → ℝ) :
    uniformMean (fun a => ∑ i ∈ J, f i a) =
      ∑ i ∈ J, uniformMean (fun a => f i a) := by
  classical
  unfold uniformMean
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_div]

private lemma truncated_eq_sum_survival {V : Type u} [Fintype V]
    (h02 : S3_02Statement.{u}) (h21 : S3_21Statement.{u})
    (q : ℕ) (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (G : MGraph V) (b : ℕ) :
    truncatedLifetime q b G = ∑ k ∈ Finset.range b, survival q G k := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card_two V hV
  have hformula := (h21 V q hq hV).2.1 G b
  rw [hformula]
  rw [uniformMean_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkb : k ≤ b := Nat.le_of_lt (Finset.mem_range.mp hk)
  let ι : Fin k ↪ Fin b :=
    ⟨fun j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkb⟩,
      fun a c heq => by
        apply Fin.ext
        simpa using congrArg Fin.val heq⟩
  have hcoord := (h02 (Pair V) b k ι).2.2.1
    (fun y : EdgeTuple V k => indicator (Colorable q (G + tupleGraph y)))
  calc
    uniformMean (fun x : EdgeTuple V b =>
        indicator (Colorable q (G + tuplePrefix x k))) =
      uniformMean (fun x : EdgeTuple V b =>
        indicator (Colorable q (G + tupleGraph (fun j => x (ι j))))) := by
          apply congrArg
          funext x
          rw [tuplePrefix_eq_tupleGraph_restrictTuple hkb x]
          rfl
    _ = uniformMean (fun y : EdgeTuple V k =>
        indicator (Colorable q (G + tupleGraph y))) := hcoord
    _ = survival q G k := rfl

private lemma ofReal_survival_eq_graphMeanENN {V : Type u} [Fintype V]
    (hpair : Nonempty (Pair V)) (q : ℕ) (G : MGraph V) (k : ℕ) :
    ENNReal.ofReal (survival q G k) =
      graphMeanENN k (fun K => if Colorable q (G + K) then 1 else 0) := by
  classical
  letI : Nonempty (Pair V) := hpair
  have hcard : 0 < Fintype.card (EdgeTuple V k) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcardR : (0 : ℝ) < (Fintype.card (EdgeTuple V k) : ℝ) := by exact_mod_cast hcard
  change ENNReal.ofReal
      ((∑ x : EdgeTuple V k, indicator (Colorable q (G + tupleGraph x))) /
        (Fintype.card (EdgeTuple V k) : ℝ)) =
    (∑ x : EdgeTuple V k, (if Colorable q (G + tupleGraph x) then 1 else 0)) /
      (Fintype.card (EdgeTuple V k) : ℝ≥0∞)
  rw [ENNReal.ofReal_div_of_pos hcardR]
  rw [ENNReal.ofReal_sum_of_nonneg (by
    intro x hx
    unfold indicator
    split_ifs <;> norm_num)]
  simp only [indicator]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : Colorable q (G + tupleGraph x) <;> simp [hp]
  norm_num

private lemma survival_relabel {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (h01 : S3_01Statement.{u, v}) (h03b : S3_03bStatement.{u, v})
    (hV : 2 ≤ Fintype.card V) (hW : 2 ≤ Fintype.card W)
    (q : ℕ) (hq : 2 ≤ q)
    (π : V ≃ W) (G : MGraph V) (k : ℕ) :
    survival q (relabel π G) k = survival q G k := by
  classical
  letI : Nonempty (Pair V) := pair_nonempty_of_card_two V hV
  letI : Nonempty (Pair W) := pair_nonempty_of_card_two W hW
  have hmean := (h03b V W hV).2.2 π k
    (fun K : MGraph W => if Colorable q (relabel π G + K) then 1 else 0)
  have hleft : graphMeanENN k
      (fun K : MGraph V => if Colorable q (relabel π G + relabel π K) then 1 else 0) =
      ENNReal.ofReal (survival q G k) := by
    rw [ofReal_survival_eq_graphMeanENN (V := V) (hpair := inferInstance) q G k]
    apply congrArg uniformMeanENN
    funext x
    change
      (if Colorable q (relabel π G + relabel π (tupleGraph x)) then 1 else 0) =
        (if Colorable q (G + tupleGraph x) then 1 else 0)
    rw [← relabel_add π G (tupleGraph x)]
    simp only [colorable_relabel h01 q hq π (G + tupleGraph x)]
  have hright : graphMeanENN k
      (fun K : MGraph W => if Colorable q (relabel π G + K) then 1 else 0) =
      ENNReal.ofReal (survival q (relabel π G) k) := by
    symm
    exact ofReal_survival_eq_graphMeanENN (V := W) (hpair := inferInstance) q
      (relabel π G) k
  rw [hleft, hright] at hmean
  have hGnonneg : 0 ≤ survival q G k := by
    unfold survival uniformProb uniformMean indicator
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _
  have hRnonneg : 0 ≤ survival q (relabel π G) k := by
    unfold survival uniformProb uniformMean indicator
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _
  exact (ENNReal.ofReal_eq_ofReal_iff hRnonneg hGnonneg).mp hmean.symm

theorem S3_22Statement_of_deps
    (h01 : S3_01Statement.{u, v})
    (h02V : S3_02Statement.{u})
    (h02W : S3_02Statement.{v})
    (h03b : S3_03bStatement.{u, v})
    (h21V : S3_21Statement.{u})
    (h21W : S3_21Statement.{v}) :
    S3_22Statement.{u, v} := by
  classical
  intro V W instV instW q hq hV hW
  letI : Fintype V := instV
  letI : Fintype W := instW
  refine ⟨?_, ?_⟩
  · intro G H hsub
    refine ⟨?_, ?_, ?_⟩
    · intro ω
      have hcharG := (h21V V q hq hV).1 G ω
      have hcharH := (h21V V q hq hV).1 H ω
      by_cases htop : freshHittingTime q G ω = ⊤
      · simp [htop]
      · have hfinite : ∃ n : ℕ, freshHittingTime q G ω = n := by
          cases ht : freshHittingTime q G ω with
          | top => exact (htop ht).elim
          | coe n => exact ⟨n, rfl⟩
        obtain ⟨n, htG⟩ := hfinite
        rw [htG]
        apply not_lt.mp
        intro hn
        have hcolorH := (hcharH n).mp hn
        have hadd : subgraph (G + processGraph ω n) (H + processGraph ω n) := by
          intro e
          exact Nat.add_le_add_right (hsub e) _
        have hcolorG := colorable_of_subgraph (V := V) (W := W) h01 q hq
          (G + processGraph ω n) (H + processGraph ω n) hadd hcolorH
        have hltG := (hcharG n).mpr hcolorG
        rw [htG] at hltG
        exact (lt_irrefl _ hltG)
    · have hsurv : ∀ k, survival q H k ≤ survival q G k :=
        fun k => survival_mono (V := V) (W := W) h01 q hq G H hsub k
      unfold lifetime
      apply ENNReal.tsum_le_tsum
      intro k
      exact ENNReal.ofReal_le_ofReal (hsurv k)
    · intro b
      rw [truncated_eq_sum_survival h02V h21V q hq hV H b,
        truncated_eq_sum_survival h02V h21V q hq hV G b]
      apply Finset.sum_le_sum
      intro k hk
      exact survival_mono (V := V) (W := W) h01 q hq G H hsub k
  · intro G π
    have hpair := pair_nonempty_of_card_two V hV
    have hlife : lifetime q (relabel π G) = lifetime q G := by
      unfold lifetime
      apply tsum_congr
      intro k
      have hs := survival_relabel h01 h03b hV hW q hq π G k
      have hnonneg : 0 ≤ survival q (relabel π G) k := by
        unfold survival uniformProb uniformMean indicator
        apply div_nonneg
        · apply Finset.sum_nonneg
          intro x hx
          split_ifs <;> norm_num
        · exact Nat.cast_nonneg _
      have hnonnegG : 0 ≤ survival q G k := by
        unfold survival uniformProb uniformMean indicator
        apply div_nonneg
        · apply Finset.sum_nonneg
          intro x hx
          split_ifs <;> norm_num
        · exact Nat.cast_nonneg _
      exact congrArg ENNReal.ofReal hs
    refine ⟨hlife, ?_, ?_⟩
    · exact congrArg ENNReal.toReal hlife
    · intro b
      rw [truncated_eq_sum_survival h02W h21W q hq hW (relabel π G) b,
        truncated_eq_sum_survival h02V h21V q hq hV G b]
      apply Finset.sum_congr rfl
      intro k hk
      exact survival_relabel h01 h03b hV hW q hq π G k

end ThLean.W.S324
