import UuSummerschool2025.Flow

namespace Flow

variable (τ : Type*) [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)

lemma union_neg_pos_semiorbit [LinearOrder τ] (ϕ : Flow τ α) (a : α) :
    negative_semiorbit ϕ a ∪ positive_semiorbit ϕ a = orbit ϕ a := by
  dsimp [negative_semiorbit, positive_semiorbit, orbit]
  apply Set.ext
  intro x
  constructor
  · intro h
    rw [Set.mem_union] at h
    obtain h | h := h
    · obtain ⟨t, ht⟩ := h
      use t
      exact ht.right
    · obtain ⟨t, ht⟩ := h
      use t
      exact ht.right
  · intro h
    obtain ⟨t, ht⟩ := h
    by_cases hgt : t ≥ 0
    · right
      use t
    · left
      simp at hgt
      use t
      constructor
      · have ha : t ≤ 0 := by exact le_of_lt hgt
        assumption
      · assumption

end Flow
