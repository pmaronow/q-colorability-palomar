module

public import ThLean.BP.S3.Poisson

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S334

private def shuffleFinset {E : Type*} [DecidableEq E] : List E → List E → Finset (List E)
  | [], v => {v}
  | a :: u, [] => {a :: u}
  | a :: u, b :: v =>
      (shuffleFinset u (b :: v)).image
        (⟨fun w => a :: w, fun x y h => by simpa using h⟩ : List E ↪ List E) ∪
      (shuffleFinset (a :: u) v).image
        (⟨fun w => b :: w, fun x y h => by simpa using h⟩ : List E ↪ List E)
termination_by u v => u.length + v.length
decreasing_by all_goals simp_wf

private theorem filter_eq_nil_of_all_false {E : Type*} (label : E → Bool) :
    ∀ l : List E, (∀ e ∈ l, label e = false) → l.filter label = []
  | [], _ => rfl
  | a :: l, h => by
      have ha : label a = false := h a (by simp)
      have hl : ∀ e ∈ l, label e = false := fun e he => h e (by simp [he])
      simp [ha, filter_eq_nil_of_all_false label l hl]

private theorem filter_not_eq_self_of_all_false {E : Type*} (label : E → Bool) :
    ∀ l : List E, (∀ e ∈ l, label e = false) → l.filter (fun e => !(label e)) = l
  | [], _ => rfl
  | a :: l, h => by
      have ha : label a = false := h a (by simp)
      have hl : ∀ e ∈ l, label e = false := fun e he => h e (by simp [he])
      simp [ha, filter_not_eq_self_of_all_false label l hl]

private theorem filter_eq_self_of_all_true {E : Type*} (label : E → Bool) :
    ∀ l : List E, (∀ e ∈ l, label e = true) → l.filter label = l
  | [], _ => rfl
  | a :: l, h => by
      have ha : label a = true := h a (by simp)
      have hl : ∀ e ∈ l, label e = true := fun e he => h e (by simp [he])
      simp [ha, filter_eq_self_of_all_true label l hl]

private theorem filter_not_eq_nil_of_all_true {E : Type*} (label : E → Bool) :
    ∀ l : List E, (∀ e ∈ l, label e = true) → l.filter (fun e => !(label e)) = []
  | [], _ => rfl
  | a :: l, h => by
      have ha : label a = true := h a (by simp)
      have hl : ∀ e ∈ l, label e = true := fun e he => h e (by simp [he])
      simp [ha, filter_not_eq_nil_of_all_true label l hl]

private theorem eq_of_filter_left_empty {E : Type*} (label : E → Bool) :
    ∀ {w v : List E}, w.filter label = [] →
      w.filter (fun e => !(label e)) = v → w = v
  | [], v, _, h => by simpa using h.symm
  | a :: w, v, h₁, h₂ => by
      have ha : label a = false := by
        cases h : label a with
        | false => rfl
        | true => simp [h] at h₁
      have h₁' : w.filter label = [] := by simpa [ha] using h₁
      have h₂' : a :: w.filter (fun e => !(label e)) = v := by
        simpa [ha] using h₂
      cases v with
      | nil => simp at h₂'
      | cons b v =>
        injection h₂' with hab htail
        subst b
        have hwv := eq_of_filter_left_empty label h₁' htail
        simp [hwv]

private theorem eq_of_filter_right_empty {E : Type*} (label : E → Bool) :
    ∀ {w u : List E}, w.filter label = u →
      w.filter (fun e => !(label e)) = [] → w = u
  | [], u, h₁, _ => by simpa using h₁.symm
  | a :: w, u, h₁, h₂ => by
      have ha : label a = true := by
        cases h : label a with
        | true => rfl
        | false => simp [h] at h₂
      have h₁' : a :: w.filter label = u := by simpa [ha] using h₁
      have h₂' : w.filter (fun e => !(label e)) = [] := by simpa [ha] using h₂
      cases u with
      | nil => simp at h₁'
      | cons b u =>
        injection h₁' with hab htail
        subst b
        have hwu := eq_of_filter_right_empty label htail h₂'
        simp [hwu]

private theorem shuffle_mem_iff {E : Type*} [DecidableEq E] (label : E → Bool) :
    ∀ (u v : List E), (∀ e ∈ u, label e = true) → (∀ e ∈ v, label e = false) →
      ∀ w : List E, w ∈ shuffleFinset u v ↔
        w.filter label = u ∧ w.filter (fun e => !(label e)) = v := by
  intro u v hu hv w
  cases u with
  | nil =>
    simp only [shuffleFinset, Finset.mem_singleton]
    constructor
    · intro hmem
      subst w
      exact ⟨filter_eq_nil_of_all_false label v hv,
        filter_not_eq_self_of_all_false label v hv⟩
    · rintro ⟨h₁, h₂⟩
      have hw : w = v := eq_of_filter_left_empty label h₁ h₂
      simp [hw]
  | cons a u =>
    cases v with
    | nil =>
      simp only [shuffleFinset, Finset.mem_singleton]
      constructor
      · intro hmem
        subst w
        exact ⟨filter_eq_self_of_all_true label (a :: u) hu,
          filter_not_eq_nil_of_all_true label (a :: u) hu⟩
      · rintro ⟨h₁, h₂⟩
        have hw : w = a :: u := eq_of_filter_right_empty label h₁ h₂
        simp [hw]
    | cons b v =>
      have ha : label a = true := hu a (by simp)
      have hb : label b = false := hv b (by simp)
      have hu' : ∀ e ∈ u, label e = true := by
        intro e he
        exact hu e (by simp [he])
      have hv' : ∀ e ∈ v, label e = false := by
        intro e he
        exact hv e (by simp [he])
      simp only [shuffleFinset, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · have ih := shuffle_mem_iff label u (b :: v) hu' hv x
          rcases ih.mp hx with ⟨h₁, h₂⟩
          change (a :: x).filter label = a :: u ∧
            (a :: x).filter (fun e => !(label e)) = b :: v
          exact ⟨by simp [ha, h₁], by simp [ha, h₂]⟩
        · have ih := shuffle_mem_iff label (a :: u) v hu hv' x
          rcases ih.mp hx with ⟨h₁, h₂⟩
          change (b :: x).filter label = a :: u ∧
            (b :: x).filter (fun e => !(label e)) = b :: v
          exact ⟨by simp [hb, h₁], by simp [hb, h₂]⟩
      · rintro ⟨h₁, h₂⟩
        cases w with
        | nil => simp at h₁
        | cons c w =>
          cases hc : label c with
          | true =>
            have h₁' : c :: w.filter label = a :: u := by
              simpa [hc] using h₁
            have hca : c = a := (List.cons.inj h₁').1
            have htail : w.filter label = u := (List.cons.inj h₁').2
            have h₂' : w.filter (fun e => !(label e)) = b :: v := by
              simpa [hc] using h₂
            have ih := shuffle_mem_iff label u (b :: v) hu' hv w
            left
            refine ⟨w, ih.mpr ⟨htail, h₂'⟩, ?_⟩
            change a :: w = c :: w
            simp [hca]
          | false =>
            have h₁' : w.filter label = a :: u := by
              simpa [hc] using h₁
            have h₂' : c :: w.filter (fun e => !(label e)) = b :: v := by
              simpa [hc] using h₂
            have hcb : c = b := (List.cons.inj h₂').1
            have htail : w.filter (fun e => !(label e)) = v := (List.cons.inj h₂').2
            have ih := shuffle_mem_iff label (a :: u) v hu hv' w
            right
            refine ⟨w, ih.mpr ⟨h₁', htail⟩, ?_⟩
            change b :: w = c :: w
            simp [hcb]
  termination_by u v => u.length + v.length
  decreasing_by
    all_goals
      subst_vars
      simp_wf


private theorem shuffle_card {E : Type*} [DecidableEq E] (label : E → Bool) :
    ∀ (u v : List E), (∀ e ∈ u, label e = true) → (∀ e ∈ v, label e = false) →
      (shuffleFinset u v).card = (u.length + v.length).choose u.length := by
  intro u v hu hv
  cases u with
  | nil => simp [shuffleFinset]
  | cons a u =>
    cases v with
    | nil => simp [shuffleFinset]
    | cons b v =>
      have ha : label a = true := hu a (by simp)
      have hb : label b = false := hv b (by simp)
      have hu' : ∀ e ∈ u, label e = true := by
        intro e he
        exact hu e (by simp [he])
      have hv' : ∀ e ∈ v, label e = false := by
        intro e he
        exact hv e (by simp [he])
      let f : List E ↪ List E := ⟨fun w => a :: w, fun _ _ h => (List.cons.inj h).2⟩
      let g : List E ↪ List E := ⟨fun w => b :: w, fun _ _ h => (List.cons.inj h).2⟩
      have hdisj : Disjoint ((shuffleFinset u (b :: v)).image f)
          ((shuffleFinset (a :: u) v).image g) := by
        apply Finset.disjoint_left.mpr
        intro w hw₁ hw₂
        obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hw₁
        obtain ⟨y, hy, hyw⟩ := Finset.mem_image.mp hw₂
        have hxy : a :: x = b :: y := by
          calc
            a :: x = f x := rfl
            _ = w := hxw
            _ = g y := hyw.symm
            _ = b :: y := rfl
        have hab : a = b := (List.cons.inj hxy).1
        have hbad : true = false := by simpa [ha, hb] using congrArg label hab
        cases hbad
      rw [shuffleFinset, Finset.card_union_of_disjoint hdisj]
      rw [Finset.card_image_of_injective _ f.injective,
        Finset.card_image_of_injective _ g.injective]
      have h₁ := shuffle_card label u (b :: v) hu' hv
      have h₂ := shuffle_card label (a :: u) v hu hv'
      rw [h₁, h₂]
      simp only [List.length_cons]
      have hp := Nat.choose_succ_succ (u.length + v.length + 1) u.length
      simpa only [Nat.add_succ, Nat.succ_add] using hp.symm
  termination_by u v => u.length + v.length
  decreasing_by
    all_goals
      subst_vars
      simp_wf

private theorem prod_map_eq_filter_products {E : Type*} (label : E → Bool) :
    ∀ (l : List E) (ν : E → ℝ),
      (l.map ν).prod = (l.filter label |>.map ν).prod *
        (l.filter (fun e => !(label e)) |>.map ν).prod := by
  intro l
  induction l with
  | nil => intro ν; simp
  | cons a l ih =>
    intro ν
    cases h : label a <;>
      simp [h, ih ν, mul_assoc, mul_left_comm]

private theorem filter_length_prod {E : Type*} {label : E → Bool} {u v w : List E}
    (h₁ : w.filter label = u)
    (h₂ : w.filter (fun e => !(label e)) = v) :
    w.length = u.length + v.length ∧
      ∀ ν : E → ℝ, (w.map ν).prod = (u.map ν).prod * (v.map ν).prod := by
  constructor
  · have h := List.length_eq_length_filter_add (l := w) label
    rw [h₁, h₂] at h
    exact h
  · intro ν
    rw [prod_map_eq_filter_products label w ν, h₁, h₂]


theorem S3_33Statement_holds : ThLean.BP.S3.S3_33Statement := by
  intro E _ label u v hu hv
  classical
  let A : Set (List E) := {w | w.filter label = u ∧ w.filter (fun e => !(label e)) = v}
  change A.Finite ∧ A.ncard = (u.length + v.length).choose u.length ∧
    ∀ w ∈ A, w.length = u.length + v.length ∧
      ∀ ν : E → ℝ, (w.map ν).prod = (u.map ν).prod * (v.map ν).prod
  have hA : A = (shuffleFinset u v : Set (List E)) := by
    ext w
    exact (shuffle_mem_iff label u v hu hv w).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact (shuffleFinset u v).finite_toSet
  · rw [hA]
    simp only [Set.ncard_coe_finset]
    exact shuffle_card label u v hu hv
  · intro w hw
    rw [hA] at hw
    change w ∈ shuffleFinset u v at hw
    have hfilters := (shuffle_mem_iff label u v hu hv w).mp hw
    exact filter_length_prod hfilters.1 hfilters.2

end ThLean.W.S334
