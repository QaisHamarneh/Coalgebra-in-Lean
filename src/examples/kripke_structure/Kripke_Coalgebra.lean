import coalgebra.Coalgebra
import examples.kripke_structure.Kripke_Structure
import set_category.category_set
import category_theory.types
import help_functions



namespace Kripe_Coalgebra

open Kripke_Structure set help_functions coalgebra


universes u v 

variable {φ : Type v}

def F : Type u ⥤ Type (max v u) := 
    {
        obj := λ S, (set S) × (set φ),
        map := λ {A B} ϕ, λ ⟨U , P⟩ , ⟨image ϕ U, P⟩,
        map_id' :=  
            begin 
                intros X, 
                dsimp at *, 
                ext1, 
                cases x with U P, 
                dsimp at *,
                ext1,
                have im : image id U = U :=  by simp,
                exact im,
                refl
            end ,
        map_comp' := 
            begin
                intros X Y Z f g,
                dsimp at *, 
                ext1, 
                cases x with S P, 
                dsimp at *, 
                calc 
                F._match_1 (g ∘ f) (S, P)
                    = ⟨image (g ∘ f) S, P⟩              : rfl
                ... = ⟨image g (image f S), P⟩          : by rw [img_comp f g S] 
                ... = F._match_1 g (F._match_1 f (S, P)) : rfl
            end
    } 

def α (K : Kripke φ): K.State → F.obj K.State := 
        λ s, ⟨K.T s,  K.v s⟩

def Kripke_Coalgebra (K : Kripke φ): Coalgebra F := 
    ⟨K.State , α K⟩ 

lemma Kripke_Coalgebra_hom {K₁ K₂ : Kripke φ} (ϕ : K₁ → K₂): 
    is_homomorphism φ ϕ ↔ 
    @is_coalgebra_homomorphism F 
        (Kripke_Coalgebra K₁) (Kripke_Coalgebra K₂)
            ϕ :=
    let 𝕂₁  := Kripke_Coalgebra K₁ in
    let 𝕂₂ := Kripke_Coalgebra K₂ in
    iff.intro 
    (
    assume ⟨tr, b_a, pr⟩,
    show 𝕂₂.α ∘ ϕ = F.map ϕ ∘ 𝕂₁.α,
    begin 
        ext1,
        have im_elem : ∀ s : K₂.State , 
                s ∈ image ϕ (K₁.T x) ↔ s ∈ K₂.T (ϕ x) :=   
            begin
                intro s,
                split,
                intros im_ϕ,
                cases im_ϕ with s12 specS12,
                rw ← specS12.2,
                exact tr x s12 specS12.1,
                intro s_T2,
                exact b_a x s s_T2,
            end,

        have im : image ϕ (K₁.T x) = K₂.T (ϕ x) := 
            eq_sets.1 im_elem,
        
        have F_ϕ : F.map ϕ (𝕂₁.α x) = ⟨image ϕ (K₁.T x), K₁.v x⟩ := rfl,
        simp [F_ϕ],
        have last : (⟨K₂.T (ϕ x) , K₂.v (ϕ x)⟩ : (set K₂.State) × set φ) = 
                        ⟨image ϕ (K₁.T x), K₁.v x⟩ := 
                by simp [eq.symm im, eq.symm (pr x)],
        simp [eq.symm last],
        refl
    end )
    (
    assume co_hom : 𝕂₂.α ∘ ϕ = F.map ϕ ∘ 𝕂₁.α,
    show (∀ a₁ a₂ :K₁ , a₂ ∈ K₁.T a₁ → (ϕ a₂) ∈ K₂.T (ϕ a₁)) ∧ 
         (∀ (a : K₁) (b : K₂) , b ∈ K₂.T (ϕ a) →
                ∃ a': K₁ ,  a' ∈ K₁.T a ∧ ϕ a' = b) ∧ 
         (∀ a : K₁ , K₁.v a = K₂.v (ϕ a)),
    begin
        split,
        intros a₁ a₂ a₂_a₁,
       
        have h3 : (𝕂₂.α ∘ ϕ) a₁ = ((F.map ϕ) ∘ 𝕂₁.α) a₁ 
                     := by rw co_hom,
        have h5 : (⟨K₂.T (ϕ a₁) , K₂.v (ϕ a₁)⟩ : (set K₂.State) × set φ) = 
                        ⟨image ϕ (K₁.T a₁), K₁.v a₁⟩ := h3,
        have h6 : K₂.T (ϕ a₁) = image ϕ (K₁.T a₁) := by tidy,
        have h7 : ϕ a₂ ∈ image ϕ (K₁.T a₁) := by {use a₂, simp [a₂_a₁]},
        rw h6,
        exact h7,

        split,
        intros a₁ b b_T_ϕ_a,
        have h3 : (𝕂₂.α ∘ ϕ) a₁ = ((F.map ϕ) ∘ 𝕂₁.α) a₁ 
                     := by rw co_hom,
        have h4 : 𝕂₂.α (ϕ a₁) = F.map ϕ (𝕂₁.α a₁) 
                     := h3,
        have h5 : (⟨K₂.T (ϕ a₁) , K₂.v (ϕ a₁)⟩ : (set K₂.State) × set φ) = 
                        ⟨image ϕ (K₁.T a₁), K₁.v a₁⟩ := h4,
        have h6 : K₂.T (ϕ a₁) = image ϕ (K₁.T a₁) := by tidy,
        have h7 : b ∈ image ϕ (K₁.T a₁) := h6 ▸ b_T_ϕ_a,
        exact h7,
        intro a₁,
        have h3 : (𝕂₂.α ∘ ϕ) a₁ = ((F.map ϕ) ∘ 𝕂₁.α) a₁ 
                     := by rw co_hom,
        have h5 : (⟨K₂.T (ϕ a₁) , K₂.v (ϕ a₁)⟩ : (set K₂.State) × set φ) = 
                        ⟨image ϕ (K₁.T a₁), K₁.v a₁⟩ := h3,
        have h6 : K₂.v (ϕ a₁) = K₁.v a₁ := by tidy,
        exact eq.symm h6
    end)
    


















end Kripe_Coalgebra