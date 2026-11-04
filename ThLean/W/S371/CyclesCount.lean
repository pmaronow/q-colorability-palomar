module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S371
open ThLean.BP.S3
open ThresholdFoundations

abbrev S3_68Code (V : Type u) (k : ℕ) :=
  Fin 2 × Fin (k + 2) × Fin (k + 2) × (Fin k ↪ V)

def S3_68Decode {V : Type u} [Fintype V] (k : ℕ) (hk : 0 < k) :
    S3_68Code V k → MGraph V
  | (shape, j₁, j₂, labels) =>
      if shape.val = 0 then
        thetaCode hk j₁.val j₂.val (k + 1 - j₁.val - j₂.val) labels
      else
        dumbbellCode hk j₁.val j₂.val (k + 1 - j₁.val - j₂.val) labels

private theorem s3_68_decode_theta {V : Type u} [Fintype V] (k j₁ j₂ j₃ : ℕ)
    (hk : 0 < k) (hsum : j₁ + j₂ + j₃ = k + 1)
    (h₁ : j₁ ≤ k + 1) (h₂ : j₂ ≤ k + 1) (labels : Fin k ↪ V) :
    S3_68Decode k hk ⟨0, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩ =
      thetaCode hk j₁ j₂ j₃ labels := by
  have hlen : k + 1 - j₁ - j₂ = j₃ := by omega
  simp [S3_68Decode, hlen]

private theorem s3_68_decode_dumbbell {V : Type u} [Fintype V] (k j₁ j₂ j₃ : ℕ)
    (hk : 0 < k) (hsum : j₁ + j₂ + j₃ = k + 1)
    (h₁ : j₁ ≤ k + 1) (h₂ : j₂ ≤ k + 1) (labels : Fin k ↪ V) :
    S3_68Decode k hk ⟨1, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩ =
      dumbbellCode hk j₁ j₂ j₃ labels := by
  have hlen : k + 1 - j₁ - j₂ = j₃ := by omega
  simp [S3_68Decode, hlen]

theorem S3_68Statement_of_deps
    (h66 : ThLean.BP.S3.S3_66Statement.{u})
    (h67 : ThLean.BP.S3.S3_67Statement.{u}) :
    ThLean.BP.S3.S3_68Statement.{u} := by
  intro V _ k hk hkn
  have hkPos : 0 < k := by omega
  let codes : Type u := S3_68Code V k
  let dec : codes → MGraph V := S3_68Decode k hkPos
  let witnesses : Set (MGraph V) := {G | Witness k G}
  have hcover : witnesses ⊆ Set.range dec := by
    intro G hG
    change Witness k G at hG
    rcases hG with ⟨_, hcard, hshape⟩
    subst k
    let k := (vertexSupport G).card
    rcases hshape with htheta | hdumbbell
    · obtain ⟨_, _, hkG, j₁, j₂, j₃, labels, hj₁, hj₂, hj₃, hsum, hcode⟩ :=
        (h66 V).1 G htheta
      have h₁ : j₁ ≤ k + 1 := by omega
      have h₂ : j₂ ≤ k + 1 := by omega
      refine ⟨⟨0, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩, ?_⟩
      change S3_68Decode k hkPos (⟨0, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩ : S3_68Code V k) = G
      rw [s3_68_decode_theta k j₁ j₂ j₃ hkG hsum h₁ h₂ labels]
      exact hcode.symm
    · obtain ⟨_, _, hkG, j₁, j₂, j₃, labels, hj₁, hj₂, hsum, hcode⟩ :=
        (h67 V).1 G hdumbbell
      have h₁ : j₁ ≤ k + 1 := by omega
      have h₂ : j₂ ≤ k + 1 := by omega
      refine ⟨⟨1, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩, ?_⟩
      change S3_68Decode k hkPos (⟨1, ⟨j₁, by omega⟩, ⟨j₂, by omega⟩, labels⟩ : S3_68Code V k) = G
      rw [s3_68_decode_dumbbell k j₁ j₂ j₃ hkG hsum h₁ h₂ labels]
      exact hcode.symm
  have hwitness_finite : witnesses.Finite := by
    apply (Set.finite_range dec).subset
    exact hcover
  have hEmb : Fintype.card (Fin k ↪ V) ≤ (Fintype.card V) ^ k := by
    calc
      Fintype.card (Fin k ↪ V) ≤ Fintype.card (Fin k → V) :=
        Fintype.card_le_of_injective (fun e : Fin k ↪ V => (e : Fin k → V))
          (fun e₁ e₂ h => Function.Embedding.ext (fun i => congrFun h i))
      _ = (Fintype.card V) ^ k := by simp
  have hcodes : Fintype.card codes ≤ 2 * (k + 2) ^ 2 * (Fintype.card V) ^ k := by
    change Fintype.card (S3_68Code V k) ≤ _
    simp only [S3_68Code, Fintype.card_prod, Fintype.card_fin]
    nlinarith [hEmb]
  have hrange : (Set.range dec).ncard ≤ Fintype.card codes := by
    rw [← Set.image_univ]
    simpa [Set.ncard_univ] using
      (Set.ncard_image_le (f := dec) (s := (Set.univ : Set codes)))
  refine ⟨hwitness_finite, ?_, ?_⟩
  · calc
      witnesses.ncard ≤ (Set.range dec).ncard := Set.ncard_le_ncard hcover (Set.finite_range dec)
      _ ≤ Fintype.card codes := hrange
      _ ≤ 2 * (k + 2) ^ 2 * (Fintype.card V) ^ k := hcodes
  · intro G hG
    rcases hG with ⟨_, hcard, hshape⟩
    rcases hshape with htheta | hdumbbell
    · obtain ⟨_, hedges, _, _, _, _, _, _, _, _⟩ := (h66 V).1 G htheta
      simpa [hcard] using hedges
    · obtain ⟨_, hedges, _, _, _, _, _, _, _⟩ := (h67 V).1 G hdumbbell
      simpa [hcard] using hedges

end ThLean.W.S371
