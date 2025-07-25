import UuSummerschool2025.Flow

namespace Flow

variable (τ : Type*) [AddMonoid τ] [TopologicalSpace τ] [ContinuousAdd τ]
  {α : Type*} [TopologicalSpace α] (ϕ : Flow τ α)

lemma union_neg_pos_semiorbit [LinearOrder τ] (ϕ : Flow τ α) (a : α) :
    negativeSemiorbit ϕ a ∪ positiveSemiorbit ϕ a = orbit ϕ a := by
  dsimp [negativeSemiorbit, positiveSemiorbit, orbit]
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

-- def ClosedNonEmptyInvariants (α : Type*) :=

variable {β : Type*}

lemma IsInvariant.biInter {s : Set β} {f : β → Set α}
    (ϕ : Flow τ α) (h: ∀ i ∈ s, IsInvariant ϕ (f i)) : IsInvariant ϕ (⋂ i ∈ s, f i) := by
  sorry

lemma IsInvariant.inter (ϕ : Flow τ α) (s1 : Set α) (s2 : Set α) (h1 : IsInvariant ϕ s1) (h2 : IsInvariant ϕ s2) :
    IsInvariant ϕ (s1 ∩ s2) := by
  sorry

lemma exists_minimal_set (ϕ : Flow τ α) [Nonempty α] [CompactSpace α] [T2Space α]:
    ∃ s : Set α, IsMinimal ϕ s := by

  let c := {t : Set α | IsClosedNonEmptyInvariant ϕ t }

  -- c is not empty
  have h1 : Nonempty c := by
    use Set.univ
    dsimp [c, IsClosedNonEmptyInvariant]
    constructor
    · exact Set.univ.nonempty
    · constructor
      · rw [isInvariant_iff_image]
        intro t
        exact fun ⦃a⦄ a ↦ trivial
      · exact isClosed_univ

  -- There is a minimal element
  have h2 : ∃ m : c, ∀ s : c, s.1 ⊆ m.1 → m.1 ⊆ s.1 := by
    -- using zorn's lemma
    apply exists_maximal_of_chains_bounded (α := c) (r := fun x y ↦ y.1 ⊆ x.1) ?_ ?_
    · intro chain
      --dsimp [IsChain]
      intro h
      let inf := ⋂ x ∈ chain, x.1
      have hin : inf ∈ c := by
        dsimp [c, IsClosedNonEmptyInvariant]
        constructor
        -- Intersection is not empty
        · have h1 : Nonempty inf := by
            dsimp [inf]
            apply Set.Nonempty.coe_sort
            apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            · --refine directedOn_range.mpr ?_
              --apply IsChain.directedOn
              unfold Directed
              dsimp
              intro x y
              let u := x.1 ∩ y.1
              have hu : u ∈ c := by sorry
              use ⟨u, hu⟩
              constructor
              · simp
                intro l
                apply Set.iInter_subset
                simp

                intro i
                intro t ht

                sorry
              · intro a
                simp
                intro h
                intro hy

                specialize h

                sorry
            · intro i
              by_cases hi : i ∈ chain
              · simp [hi]
                dsimp [c, IsClosedNonEmptyInvariant] at i
                obtain ⟨ha, hb, hc⟩ := i
                simp
                exact Set.Nonempty.of_subtype
              · simp [hi]
            · intro i
              by_cases hi : i ∈ chain
              · simp [hi]
                dsimp [c, IsClosedNonEmptyInvariant] at i
                obtain ⟨ha, hb, hc, hcc⟩ := i
                exact IsClosed.isCompact hcc
              · simp [hi]
                exact CompactSpace.isCompact_univ
            · intro i
              by_cases hi : i ∈ chain
              · simp [hi]
                dsimp [c, IsClosedNonEmptyInvariant] at i
                obtain ⟨ha, hb, hc, hcc⟩ := i
                exact hcc
              · simp [hi]
          assumption
        · constructor
          -- intersection is minimal again
          · have hinfi : ∀ t ∈ chain, IsInvariant ϕ t.1 := by
              intro t ht
              have htt := t.2
              dsimp [c, IsClosedNonEmptyInvariant] at htt
              obtain ⟨_, h, _⟩ := htt
              exact h
            exact IsInvariant.biInter τ ϕ hinfi
          -- intersection is closed again
          · have hinfc : ∀ t ∈ chain, IsClosed t.1 := by
              intro t ht
              have htt := t.2
              dsimp [c, IsClosedNonEmptyInvariant] at htt
              obtain ⟨_, _, h⟩ := htt
              exact h
            exact isClosed_biInter hinfc
      use ⟨inf, hin⟩
      intro a ha
      exact Set.biInter_subset_of_mem ha
    · exact fun {a b c_2} a a_1 ⦃a_2⦄ a_3 ↦ a (a_1 a_3)

  -- Show that the element is minimal
  obtain ⟨m, hm⟩ := h2
  use m
  dsimp [IsMinimal]
  constructor
  · dsimp [c] at m
    obtain ⟨m, hm⟩ := m
    assumption
  · intro h
    obtain ⟨t, ht⟩ := h
    obtain ⟨ha, hb, hc⟩ := ht
    specialize hm ⟨t, hc⟩ ha
    have h1 : m = t := by exact Set.Subset.antisymm hm ha
    exact hb (id (Eq.symm h1))


end Flow
