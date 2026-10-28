import ThLean.BP.S5.Elementary

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S506

open ThLean.BP.S5

private abbrev OutsideLetter (E : Type) (e : E) := {v : E // v ≠ e}

private abbrev LetterPositions {E : Type} [Fintype E] (c : E → ℕ) (e : E) :=
  {s : Finset (Fin (∑ v, c v)) // s.card = c e}

private abbrev SplitCondition {E : Type} [Fintype E] (c : E → ℕ) (e : E)
    (s : LetterPositions c e) (y : Fin (∑ v, c v) → Option (OutsideLetter E e)) : Prop :=
  (∀ i, y i = none ↔ i ∈ s.1) ∧
  ∀ v, (Finset.univ.filter (fun i => y i = some v)).card = c v.val

private abbrev RemainingWord {E : Type} [Fintype E] (c : E → ℕ) (e : E)
    (s : LetterPositions c e) :=
  {y : Fin (∑ v, c v) → Option (OutsideLetter E e) // SplitCondition c e s y}

private abbrev SplitWord {E : Type} [Fintype E] (c : E → ℕ) (e : E) :=
  {p : LetterPositions c e × (Fin (∑ v, c v) → Option (OutsideLetter E e)) //
    SplitCondition c e p.1 p.2}

private def wordSplitEquiv {E : Type} [Fintype E] (c : E → ℕ) (e : E) :
    {x : Fin (∑ v, c v) → E //
      ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c v} ≃ SplitWord c e := by
  classical
  let n := ∑ v, c v
  let pos (x : Fin n → E) := Finset.univ.filter (fun i => x i = e)
  let encode (x : Fin n → E) : Fin n → Option (OutsideLetter E e) := fun i =>
    if h : x i = e then none else some ⟨x i, h⟩
  let decode (y : Fin n → Option (OutsideLetter E e)) : Fin n → E :=
    fun i => y i |>.elim e Subtype.val
  refine
    { toFun := fun x => ⟨(⟨pos x.1, ?_⟩, encode x.1), ?_⟩
      invFun := fun p => ⟨decode p.1.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa [pos, n] using x.2 e
  · constructor
    · intro i
      simp [encode, pos]
    · intro v
      let hfiber : {i : Fin n // x.1 i = v.val} ≃
          {i : Fin n // encode x.1 i = some v} := by
        refine
          { toFun := fun i => ⟨i.val, ?_⟩
            invFun := fun i => ⟨i.val, ?_⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro i; apply Subtype.ext; rfl }
        · have hne : x.1 i.val ≠ e := fun h => v.property (i.property.symm.trans h)
          have hsub : (⟨x.1 i.val, hne⟩ : OutsideLetter E e) = v := by
            apply Subtype.ext
            exact i.property
          simp [encode, hne, hsub]
        · by_cases h : x.1 i.val = e
          · have hbad := i.property
            simp [encode, h] at hbad
          · have hsub : (⟨x.1 i.val, h⟩ : OutsideLetter E e) = v := by
              simpa [encode, h] using i.property
            exact congrArg Subtype.val hsub
      have hx : Fintype.card {i : Fin n // x.1 i = v.val} = c v.val := by
        simpa [Fintype.card_subtype] using x.2 v.val
      have hc := Fintype.card_congr hfiber
      have hy : Fintype.card {i : Fin n // encode x.1 i = some v} = c v.val := hc.symm.trans hx
      simpa [encode, Fintype.card_subtype] using hy
  · intro v
    let s := p.1.1.1
    let y := p.1.2
    let decode' := decode y
    by_cases hv : v = e
    · subst v
      let hfiber : {i : Fin n // decode' i = e} ≃ {i : Fin n // i ∈ s} := by
        refine
          { toFun := fun i => ⟨i.val, ?_⟩
            invFun := fun i => ⟨i.val, ?_⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro i; apply Subtype.ext; rfl }
        · cases h : y i.val with
          | none => exact (p.2.1 i.val).1 h
          | some w =>
              have heq := i.property
              simp [decode', decode, h] at heq
              exact False.elim (w.property heq)
        · have hn : y i.val = none := (p.2.1 i.val).2 i.property
          simp [decode', decode, hn]
      have hc := Fintype.card_congr hfiber
      have hs : Fintype.card {i : Fin n // i ∈ s} = c e := by
        simpa [Fintype.card_subtype] using p.1.1.2
      have ht : Fintype.card {i : Fin n // decode' i = e} = c e := hc.trans hs
      simpa [decode', Fintype.card_subtype] using ht
    · let ov : OutsideLetter E e := ⟨v, hv⟩
      let hfiber : {i : Fin n // decode' i = v} ≃ {i : Fin n // y i = some ov} := by
        refine
          { toFun := fun i => ⟨i.val, ?_⟩
            invFun := fun i => ⟨i.val, ?_⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro i; apply Subtype.ext; rfl }
        · cases h : y i.val with
          | none =>
              have heq := i.property
              simp [decode', decode, h] at heq
              exact False.elim (hv heq.symm)
          | some w =>
              have hval : w.val = v := by simpa [decode', decode, h] using i.property
              have hw : w = ov := Subtype.ext hval
              simpa [h, hw]
        · have heq := i.property
          simpa [decode', decode, heq, ov]
      have hc := Fintype.card_congr hfiber
      have hy : Fintype.card {i : Fin n // y i = some ov} = c ov.val := by
        simpa [Fintype.card_subtype] using p.2.2 ov
      have ht : Fintype.card {i : Fin n // decode' i = v} = c v := by
        simpa [ov] using hc.trans hy
      simpa [decode', Fintype.card_subtype] using ht
  · intro x
    apply Subtype.ext
    funext i
    by_cases h : x.1 i = e <;> simp [encode, decode, h]
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext i
      change i ∈ pos (decode p.1.2) ↔ i ∈ p.1.1.1
      constructor
      · intro h
        have heq : decode p.1.2 i = e := by simpa [pos] using h
        cases hy : p.1.2 i with
        | none => exact (p.2.1 i).1 hy
        | some v =>
            have hv : v.val = e := by simpa [decode, hy] using heq
            exact False.elim (v.property hv)
      · intro hi
        have hn : p.1.2 i = none := (p.2.1 i).2 hi
        simpa [pos, decode, hn]
    · funext i
      cases h : p.1.2 i with
      | none => simp [encode, decode, h]
      | some v => simp [encode, decode, h, v.property]

private theorem letterPositions_card {E : Type} [Fintype E] (c : E → ℕ) (e : E) :
    Fintype.card (LetterPositions c e) = (∑ v, c v).choose (c e) := by
  classical
  let n := ∑ v, c v
  let f : LetterPositions c e ≃
      {s : Finset (Fin n) // s ∈ (Finset.univ : Finset (Fin n)).powersetCard (c e)} :=
    { toFun := fun s => ⟨s.1, by simp [Finset.mem_powersetCard, s.2]⟩
      invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      left_inv := by intro s; apply Subtype.ext; rfl
      right_inv := by intro s; apply Subtype.ext; rfl }
  rw [Fintype.card_congr f]
  rw [Fintype.card_subtype]
  simpa [n] using Finset.card_powersetCard (c e) (Finset.univ : Finset (Fin n))

private theorem outsideSum {E : Type} [Fintype E] (c : E → ℕ) (e : E) :
    (∑ v : OutsideLetter E e, c v.val) = (∑ v, c v) - c e := by
  classical
  letI : Subsingleton {v : E // ¬v ≠ e} := ⟨fun a b => Subtype.ext (by
    have ha : a.val = e := by simpa using a.property
    have hb : b.val = e := by simpa using b.property
    exact ha.trans hb.symm)⟩
  have heq : (∑ v : {v : E // ¬v ≠ e}, c v.val) = c e := by
    rw [Fintype.sum_subsingleton _ ⟨e, by simp⟩]
  have h := Fintype.sum_subtype_add_sum_subtype (fun v : E => v ≠ e) c
  have hsum : (∑ v : OutsideLetter E e, c v.val) + c e = ∑ v, c v := by
    simpa [OutsideLetter, heq] using h
  omega

private abbrev WordOn {I : Type} [Fintype I] (O : Type) (c : O → ℕ) :=
  {x : I → O // ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c v}

private theorem remainingWord_card {E : Type} [Fintype E] (c : E → ℕ) (e : E)
    (s : LetterPositions c e) :
    Fintype.card (RemainingWord c e s) =
      wordFiberCard (fun v : OutsideLetter E e => c v.val) := by
  classical
  let O := OutsideLetter E e
  let n := ∑ v, c v
  let m := ∑ v : O, c v.val
  let T := {i : Fin n // i ∉ s.1}
  have ht : Fintype.card T = m := by
    rw [Fintype.card_subtype_compl]
    have hpos : Fintype.card {i : Fin n // i ∈ s.1} = c e := by
      simpa [Fintype.card_subtype] using s.property
    simpa [Fintype.card_fin, hpos, n] using (outsideSum c e).symm
  let q : Fin m ≃ T := (Fintype.equivOfCardEq (by simpa using ht)).symm
  let get (y : RemainingWord c e s) (i : T) : O :=
    (y.1 i.val).get (by
      cases h : y.1 i.val with
      | none => exact False.elim (i.property ((y.2.1 i.val).1 h))
      | some _ => rfl)
  let restrict : RemainingWord c e s ≃ WordOn (I := T) O (fun v => c v.val) := by
    refine
      { toFun := fun y => ⟨fun i => get y i, ?_⟩
        invFun := fun f => ⟨fun i => if hi : i ∈ s.1 then none else some (f.1 ⟨i, hi⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro v
      let f : {i : T // get y i = v} ≃ {i : Fin n // y.1 i = some v} := by
        refine
          { toFun := fun i => ⟨i.val.val, ?_⟩
            invFun := fun i => ⟨⟨i.val, ?_⟩, ?_⟩
            left_inv := ?_
            right_inv := ?_ }
        · cases h : y.1 i.val.val with
          | none => exact False.elim (i.val.property ((y.2.1 i.val.val).1 h))
          | some w =>
              have hprop := i.property
              change get y i.val = v at hprop
              simp [get, h] at hprop
              have hw : w = v := hprop
              simpa [h, hw]
        · intro hs
          have hn := (y.2.1 i.val).2 hs
          have hprop := i.property
          rw [hn] at hprop
          simp at hprop
        · have hsome : y.1 i.val = some v := i.property
          change (y.1 i.val).get _ = v
          exact Option.get_of_eq_some (by simp [hsome]) hsome
        · intro i
          apply Subtype.ext
          rfl
        · intro i
          apply Subtype.ext
          rfl
      have hc := Fintype.card_congr f
      have hfull : Fintype.card {i : Fin n // y.1 i = some v} = c v.val := by
        simpa [Fintype.card_subtype] using y.2.2 v
      have hT : Fintype.card {i : T // get y i = v} = c v.val := hc.trans hfull
      simpa [Fintype.card_subtype] using hT
    · constructor
      · intro i
        by_cases hi : i ∈ s.1
        · simp [hi]
        · simp [hi]
      · intro v
        let fib : {i : Fin n // (if hi : i ∈ s.1 then none else some (f.1 ⟨i, hi⟩)) = some v} ≃
            {i : T // f.1 i = v} := by
          refine
            { toFun := fun i => ⟨⟨i.val, ?_⟩, ?_⟩
              invFun := fun i => ⟨i.val.val, ?_⟩
              left_inv := ?_
              right_inv := ?_ }
          · intro hi
            have hprop := i.property
            simp [hi] at hprop
          · have hi : i.val ∉ s.1 := by
              intro hs
              have hprop := i.property
              simp [hs] at hprop
            have hprop := i.property
            simpa [hi] using hprop
          · have hnot := i.val.property
            simpa [hnot] using congrArg (fun a : O => some a) i.property
          · intro i
            apply Subtype.ext
            rfl
          · intro i
            apply Subtype.ext
            rfl
        have hc := Fintype.card_congr fib
        have hT : Fintype.card {i : T // f.1 i = v} = c v.val := by
          simpa [Fintype.card_subtype] using f.2 v
        have hfull : Fintype.card
            {i : Fin n // (if hi : i ∈ s.1 then none else some (f.1 ⟨i, hi⟩)) = some v} = c v.val :=
          hc.trans hT
        simpa [Fintype.card_subtype] using hfull
    · intro y
      apply Subtype.ext
      funext i
      cases h : y.1 i with
      | none => simp [h, (y.2.1 i).1 h]
      | some v =>
          have hnot : i ∉ s.1 := by
            intro hi
            have hn := (y.2.1 i).2 hi
            simp [h] at hn
          have hget : get y ⟨i, hnot⟩ = v := by
            simp [get, h]
          simp [h, hnot, hget]
    · intro f
      apply Subtype.ext
      funext i
      have hnot := i.property
      simp [get, hnot]
  let toFin : WordOn (I := T) O (fun v => c v.val) ≃
      WordOn (I := Fin m) O (fun v => c v.val) := by
    refine
      { toFun := fun w => ⟨w.1 ∘ q, ?_⟩
        invFun := fun x => ⟨x.1 ∘ q.symm, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro v
      let fib : {i : T // w.1 i = v} ≃ {i : Fin m // w.1 (q i) = v} :=
        { toFun := fun i => ⟨q.symm i.val, by simpa using i.property⟩
          invFun := fun i => ⟨q i.val, by simpa using i.property⟩
          left_inv := by intro i; apply Subtype.ext; simp
          right_inv := by intro i; apply Subtype.ext; simp }
      have hs : Fintype.card {i : T // w.1 i = v} = c v.val := by
        simpa [Fintype.card_subtype] using w.2 v
      have hc := Fintype.card_congr fib
      have ht : Fintype.card {i : Fin m // w.1 (q i) = v} = c v.val := hc.symm.trans hs
      simpa [Fintype.card_subtype] using ht
    · intro v
      let fib : {i : T // x.1 (q.symm i) = v} ≃ {i : Fin m // x.1 i = v} :=
        { toFun := fun i => ⟨q.symm i.val, by simpa using i.property⟩
          invFun := fun i => ⟨q i.val, by simpa using i.property⟩
          left_inv := by intro i; apply Subtype.ext; simp
          right_inv := by intro i; apply Subtype.ext; simp }
      have hs : Fintype.card {i : Fin m // x.1 i = v} = c v.val := by
        simpa [Fintype.card_subtype] using x.2 v
      have hc := Fintype.card_congr fib
      have ht : Fintype.card {i : T // x.1 (q.symm i) = v} = c v.val := hc.trans hs
      simpa [Fintype.card_subtype] using ht
    · intro y
      apply Subtype.ext
      funext i
      simp
    · intro x
      apply Subtype.ext
      funext i
      simp
  have hEquiv := restrict.trans toFin
  rw [Fintype.card_congr hEquiv]
  unfold wordFiberCard
  let canon : WordOn (I := Fin m) O (fun v => c v.val) ≃
      {x : Fin (∑ v : OutsideLetter E e, c v.val) → OutsideLetter E e //
        ∀ v, (Finset.univ.filter (fun i => x i = v)).card =
          (fun w : OutsideLetter E e => c w.val) v} :=
    { toFun := fun x => ⟨x.1, by simpa [WordOn, m, O] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa [WordOn, m, O] using x.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  have hcanon := Fintype.card_congr canon
  simpa [WordOn, m, O, wordFiberCard] using hcanon

theorem S5_E02AStatement_holds : S5_E02AStatement := by
  intro E hE c e
  classical
  letI := hE
  change Fintype.card
    {x : Fin (∑ v, c v) → E //
      ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c v} = _
  let decomp := Equiv.subtypeProdEquivSigmaSubtype
    (fun s : LetterPositions c e => fun y : Fin (∑ v, c v) → Option (OutsideLetter E e) =>
      SplitCondition c e s y)
  rw [Fintype.card_congr (wordSplitEquiv c e)]
  rw [Fintype.card_congr decomp]
  rw [Fintype.card_sigma]
  simp_rw [remainingWord_card]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [letterPositions_card]
  simp

end ThLean.W.S506
