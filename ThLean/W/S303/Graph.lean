import ThLean.BP.S3.Graph
import ThLean.BP.S3.Process

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.W.S303
open ThLean.BP.S3 ThresholdFoundations

theorem uniformProb_eq_card_div {α : Type*} [Fintype α]
    (P : α → Prop) :
    uniformProb P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  simp [uniformProb, uniformMean, indicator]

theorem uniformProb_not {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) :
    uniformProb (fun a => ¬ P a) = 1 - uniformProb P := by
  classical
  have hpoint (a : α) : indicator (¬ P a) + indicator (P a) = 1 := by
    by_cases h : P a <;> simp [indicator, h]
  rw [eq_sub_iff_add_eq]
  unfold uniformProb
  change uniformMean (fun a => indicator (¬ P a)) +
      uniformMean (fun a => indicator (P a)) = 1
  calc
    _ = uniformMean (fun a => indicator (¬ P a) + indicator (P a)) := by
      unfold uniformMean
      rw [Finset.sum_add_distrib, add_div]
    _ = uniformMean (fun _ : α => (1 : ℝ)) := by
      congr 1
      funext a
      exact hpoint a
    _ = 1 := by
      unfold uniformMean
      simp [Finset.sum_const, Fintype.card_pos_iff.mpr inferInstance]

theorem binomialWeight_nonneg (m k : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ 1-p) : 0 ≤ binomialWeight m p k := by
  unfold binomialWeight
  split_ifs <;> positivity

theorem binomialWeight_succ (m k : ℕ) (p : ℝ) :
    binomialWeight (m+1) p k =
      binomialWeight m p k * (1-p) +
        (if k = 0 then 0 else binomialWeight m p (k-1) * p) := by
  by_cases hk0 : k = 0
  · subst k
    simp [binomialWeight]
    rw [pow_succ]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkm : k ≤ m
    · have hpred : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      have hpredle : k - 1 ≤ m := by omega
      have hexp₁ : m + 1 - k = m - k + 1 := by omega
      have hexp₂ : m - (k - 1) = m - k + 1 := by omega
      have hk1 : k ≤ m+1 := by omega
      have hchoose : (m+1).choose k = m.choose k + m.choose (k-1) := by
        rw [show k = (k-1)+1 by omega, Nat.choose_succ_succ]
        simp [hpred, add_comm]
      have hpow₁ : p ^ k = p ^ (k-1) * p := by
        calc
          p ^ k = p ^ (k-1+1) := (congrArg (fun n : ℕ => p ^ n) hpred).symm
          _ = p ^ (k-1) * p := by rw [pow_succ]
      have hpow₂ : (1-p)^(m-k+1) = (1-p)^(m-k) * (1-p) := by
        rw [show m-k+1 = (m-k)+1 by omega, pow_succ]
      simp only [binomialWeight, if_pos hk1, if_pos hkm, if_pos hpredle,
        if_neg hk0]
      rw [hchoose, hexp₁, hexp₂, hpow₂, hpow₁]
      push_cast
      ring
    · by_cases hks : k ≤ m+1
      · have hk : k = m+1 := by omega
        subst k
        simp [binomialWeight, Nat.choose_self]
        rw [pow_succ]
      · have hpred : ¬ k-1 ≤ m := by omega
        simp [binomialWeight, hkm, hks, hpred, hk0]

theorem uniformMeanENN_indicator {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) :
    uniformMeanENN (fun a => if P a then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal (uniformProb P) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hnum :
      (∑ a : α, if P a then (1 : ℝ≥0∞) else 0) =
        ((∑ a : α, if P a then 1 else 0 : ℕ) : ℝ≥0∞) := by norm_cast
  have hsum : (∑ a : α, if P a then 1 else 0 : ℕ) =
      (Finset.univ.filter P).card := by
    symm
    simpa using (Finset.card_filter P (Finset.univ : Finset α))
  unfold uniformMeanENN
  rw [hnum, hsum]
  calc
    ((↑(Finset.univ.filter P).card : ℝ≥0∞) / Fintype.card α) =
        ENNReal.ofReal (((Finset.univ.filter P).card : ℝ) / Fintype.card α) := by
          rw [ENNReal.ofReal_div_of_pos hcard]
          norm_cast
    _ = ENNReal.ofReal (uniformProb P) := by rw [uniformProb_eq_card_div]

def touchCount {V : Type u} [Fintype V] {m : ℕ}
    (u : V) (x : EdgeTuple V m) : ℕ :=
  (Finset.univ.filter (fun i => Touches u (x i).val)).card

theorem degree_tupleGraph_eq_touchCount {V : Type u} [Fintype V]
    {m : ℕ} (u : V) (x : EdgeTuple V m) :
    degree (tupleGraph x) u = touchCount u x := by
  classical
  unfold degree tupleGraph touchCount
  simpa [Finset.sum_filter] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (Fin m)))
      (t := Finset.univ.filter (Touches u))
      (g := fun i => (x i).val))

theorem touchCount_eq_sum {V : Type u} [Fintype V] {m : ℕ}
    (u : V) (x : EdgeTuple V m) :
    touchCount u x = ∑ i : Fin m, if Touches u (x i).val then 1 else 0 := by
  classical
  change (Finset.univ.filter (fun i : Fin m => Touches u (x i).val)).card = _
  simpa using (Finset.card_filter (fun i : Fin m => Touches u (x i).val)
    (Finset.univ : Finset (Fin m)))

theorem touchCount_snoc {V : Type u} [Fintype V] {m : ℕ}
    (u : V) (x : EdgeTuple V (m+1)) :
    touchCount u x = touchCount u (fun i => x i.castSucc) +
      (if Touches u (x (Fin.last m)).val then 1 else 0) := by
  rw [touchCount_eq_sum, touchCount_eq_sum]
  rw [Fin.sum_univ_castSucc]

theorem uniformMeanENN_add {α : Type*} [Fintype α]
    (f g : α → ℝ≥0∞) :
    uniformMeanENN (fun a => f a + g a) = uniformMeanENN f + uniformMeanENN g := by
  unfold uniformMeanENN
  rw [Finset.sum_add_distrib, ENNReal.add_div]

private theorem uniformMeanENN_equiv {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ≥0∞) :
    uniformMeanENN (f ∘ e) = uniformMeanENN f := by
  unfold uniformMeanENN
  change (∑ a : α, f (e a)) / Fintype.card α = _
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

theorem uniformMeanENN_snoc_prod {E : Type u} [Fintype E] [Nonempty E]
    (h02 : ThLean.BP.S3.S3_02Statement.{u}) (m : ℕ)
    (f : (Fin m → E) → ℝ≥0∞) (g : E → ℝ≥0∞) :
    uniformMeanENN (fun x : Fin (m+1) → E =>
      f (fun i => x i.castSucc) * g (x (Fin.last m))) =
      uniformMeanENN f * uniformMeanENN g := by
  let i : Fin m ↪ Fin (m+1) := Fin.castSuccEmb
  let j : Fin 1 ↪ Fin (m+1) :=
    ⟨fun _ => Fin.last m, by intro a b _; exact Subsingleton.elim _ _⟩
  have hdis : Disjoint (Set.range i) (Set.range j) := by
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    rcases hz₁ with ⟨a, rfl⟩
    rcases hz₂ with ⟨b, hb⟩
    have heq : a.castSucc = Fin.last m := by
      change Fin.last m = i a at hb
      simpa [i] using hb.symm
    exact (Fin.castSucc_ne_last a) heq
  let g' : (Fin 1 → E) → ℝ≥0∞ := fun y => g (y 0)
  have hfactor := (h02 E (m+1) m i).2.2.2 m 1 i j hdis f g'
  have hlast' : uniformMeanENN g' = uniformMeanENN g := by
    change uniformMeanENN (g ∘ (Equiv.funUnique (Fin 1) E)) = _
    exact uniformMeanENN_equiv (Equiv.funUnique (Fin 1) E) g
  calc
    uniformMeanENN (fun x : Fin (m+1) → E =>
        f (fun i => x i.castSucc) * g (x (Fin.last m))) =
      uniformMeanENN (fun y : Fin (m+1) → E => f (fun a => y (i a)) * g' (fun b => y (j b))) := by
        congr 1
    _ = uniformMeanENN f * uniformMeanENN g' := by
      simpa using hfactor
    _ = uniformMeanENN f * uniformMeanENN g := by rw [hlast']

private def pairRelabelEquiv {V : Type u} {W : Type v} (π : V ≃ W) :
    Pair V ≃ Pair W where
  toFun e := ⟨Sym2.map π e.val, by
    intro w hw
    have hsource : e.val = s(π.symm w, π.symm w) := by
      apply (Sym2.map.injective π.injective)
      simpa using hw
    exact e.property (π.symm w) hsource⟩
  invFun e := ⟨Sym2.map π.symm e.val, by
    intro w hw
    have hsource : e.val = s(π w, π w) := by
      apply (Sym2.map.injective π.symm.injective)
      simpa using hw
    exact e.property (π w) hsource⟩
  left_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]

private theorem tupleGraph_pairRelabel {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] {m : ℕ} (π : V ≃ W) (x : EdgeTuple V m) :
    tupleGraph (fun i => pairRelabelEquiv π (x i)) = relabel π (tupleGraph x) := by
  classical
  funext e'
  change
    (Finset.univ.filter (fun i : Fin m => Sym2.map π ((x i).val) = e')).card =
      ∑ a : Sym2 V, if Sym2.map π a = e' then
        (Finset.univ.filter (fun i : Fin m => (x i).val = a)).card else 0
  rw [← Finset.sum_filter]
  simpa only [Finset.mem_filter, Finset.mem_univ, and_true, true_and] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (Fin m)))
      (t := Finset.univ.filter (fun e : Sym2 V => Sym2.map π e = e'))
      (g := fun i => (x i).val)).symm

theorem graphMeanENN_relabel {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] (π : V ≃ W) (m : ℕ) (f : MGraph W → ℝ≥0∞) :
    graphMeanENN m (fun G => f (relabel π G)) = graphMeanENN m f := by
  let e : EdgeTuple V m ≃ EdgeTuple W m :=
    Equiv.arrowCongr (Equiv.refl (Fin m)) (pairRelabelEquiv π)
  have hgraph (x : EdgeTuple V m) : tupleGraph (e x) = relabel π (tupleGraph x) := by
    change tupleGraph (fun i => pairRelabelEquiv π (x i)) = _
    exact tupleGraph_pairRelabel π x
  change uniformMeanENN (fun x : EdgeTuple V m => f (relabel π (tupleGraph x))) = _
  calc
    uniformMeanENN (fun x : EdgeTuple V m => f (relabel π (tupleGraph x))) =
        uniformMeanENN (fun x => f (tupleGraph (e x))) := by
      congr 1
      funext x
      rw [hgraph x]
    _ = uniformMeanENN (fun x : EdgeTuple W m => f (tupleGraph x)) :=
      uniformMeanENN_equiv e (fun x => f (tupleGraph x))

theorem touches_uniformProb {V : Type u} [Fintype V]
    (h03a : ThLean.BP.S3.S3_03aStatement.{u})
    (hn : 2 ≤ Fintype.card V) (a : V) :
    uniformProb (fun e : Pair V => Touches a e.val) = 2 / Fintype.card V := by
  have ha := h03a V hn
  rw [uniformProb_eq_card_div]
  have htouch :
      ((Finset.univ.filter (fun e : Pair V => Touches a e.val)).card : ℝ) =
        (Fintype.card V - 1 : ℕ) := by exact_mod_cast ha.2.2 a
  have hpairs : (Fintype.card (Pair V) : ℝ) = ((Fintype.card V).choose 2 : ℝ) :=
    by exact_mod_cast ha.1
  rw [htouch, hpairs]
  have hn' : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn'
  have hn1N : 1 < Fintype.card V := by omega
  have hn1' : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
    have h : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn1N
    linarith
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_choose_two]
  push_cast
  field_simp [ne_of_gt hnR, ne_of_gt hn1']
  <;> ring

end ThLean.W.S303
