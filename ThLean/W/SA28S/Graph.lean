module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA28S
open ThresholdFoundations

theorem isColoring_map_iff {V W : Type} [Fintype V] [Fintype W]
    (f : V → W) (q : ℕ) (G : MGraph V) (σ : W → Fin q) :
    IsColoring q (mapGraph f G) σ ↔ IsColoring q G (σ ∘ f) := by
  constructor
  · intro h u v huv
    apply h (f u) (f v)
    have ht : G s(u,v) ≤ mapGraph f G s(f u, f v) := by
      unfold mapGraph
      calc
        G s(u,v) = (if Sym2.map f s(u,v) = s(f u,f v) then G s(u,v) else 0) := by simp
        _ ≤ ∑ e : Sym2 V, if Sym2.map f e = s(f u,f v) then G e else 0 :=
          Finset.single_le_sum
            (f := fun e : Sym2 V => if Sym2.map f e = s(f u,f v) then G e else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    exact lt_of_lt_of_le huv ht
  · intro h u v huv
    obtain ⟨e, _, he⟩ := Finset.sum_pos_iff_of_nonneg (fun e _ => Nat.zero_le _) |>.mp huv
    have hg : 0 < G e ∧ Sym2.map f e = s(u,v) := by
      split_ifs at he with heq
      · exact ⟨he, heq⟩
      · omega
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hh := h a b hg.1
      rcases Sym2.eq_iff.mp hg.2 with hh' | hh'
      · simpa [Function.comp_def, hh'.1, hh'.2] using hh
      · simpa [Function.comp_def, hh'.1, hh'.2] using hh.symm

theorem isColoring_add_iff {V : Type} [Fintype V]
    (q : ℕ) (G H : MGraph V) (σ : V → Fin q) :
    IsColoring q (G + H) σ ↔ IsColoring q G σ ∧ IsColoring q H σ := by
  constructor
  · intro h
    exact ⟨fun u v huv => h u v (by change 0 < G _ + H _; omega),
      fun u v huv => h u v (by change 0 < G _ + H _; omega)⟩
  · rintro ⟨hG, hH⟩ u v huv
    have hp : 0 < G s(u,v) ∨ 0 < H s(u,v) := by
      change 0 < G _ + H _ at huv
      omega
    exact hp.elim (hG u v) (hH u v)

theorem colorable_blocks_iff (q n₁ n₂ : ℕ)
    (G : MGraph (Fin n₁)) (H : MGraph (Fin n₂)) :
    Colorable q (mapGraph (leftVertex n₁ n₂) G + mapGraph (rightVertex n₁ n₂) H) ↔
      Colorable q G ∧ Colorable q H := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hG, hH⟩ := (isColoring_add_iff _ _ _ _).mp hσ
    exact ⟨⟨σ ∘ leftVertex n₁ n₂, (isColoring_map_iff _ _ _ _).mp hG⟩,
      ⟨σ ∘ rightVertex n₁ n₂, (isColoring_map_iff _ _ _ _).mp hH⟩⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨Fin.append σ τ, (isColoring_add_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · apply (isColoring_map_iff _ _ _ _).mpr
      have he : (Fin.append σ τ) ∘ leftVertex n₁ n₂ = σ := by
        funext v
        change Fin.append σ τ (Fin.castAdd n₂ v) = σ v
        exact Fin.append_left σ τ v
      rwa [he]
    · apply (isColoring_map_iff _ _ _ _).mpr
      have he : (Fin.append σ τ) ∘ rightVertex n₁ n₂ = τ := by
        funext v
        change Fin.append σ τ (Fin.natAdd n₁ v) = τ v
        exact Fin.append_right σ τ v
      rwa [he]

end ThLean.W.SA28S
