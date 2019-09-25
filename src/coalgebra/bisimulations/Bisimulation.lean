import set_category.category_set
import coalgebra.Coalgebra
import help_functions

universe u


namespace Bisimulation

open category_theory set category_set coalgebra function classical
    help_functions

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

variables {F : Type u ⥤ Type u}
        {𝔸 Β ℂ : Coalgebra F} {A B : Type u}

 
def rel_to_set (R : 𝔸 → Β → Prop) : set (𝔸 × Β) := 
    λ ⟨a, b⟩ , R a b 


def is_bisimulation_rel (R : 𝔸 → Β → Prop) : Prop := 
    let S := rel_to_set R in 
    ∃ ρ : S → F.obj S, 
    let ℝ : Coalgebra F := ⟨S , ρ⟩ in
    let π₁ : ℝ → 𝔸 := λ r, r.val.1 in
    let π₂ : ℝ → Β := λ r, r.val.2 in
    is_coalgebra_homomorphism π₁ ∧ is_coalgebra_homomorphism π₂

def is_bisimulation (R : set (𝔸 × Β)) : Prop := 
    ∃ ρ : R → F.obj R, 
    let ℝ : Coalgebra F := ⟨R , ρ⟩ in
    let π₁ : ℝ → 𝔸 := λ r, r.val.1 in
    let π₂ : ℝ → Β := λ r, r.val.2 in
    is_coalgebra_homomorphism π₁ ∧ is_coalgebra_homomorphism π₂

theorem homomorphism_iff_bisimulation (f : 𝔸 → Β):
    is_coalgebra_homomorphism f ↔ is_bisimulation (map_to_graph f) 
    := 
    let R : set (𝔸 × Β) := map_to_graph f in
    let π₁ : R → 𝔸 := λ r, r.val.1 in 
    let π₂ : R → Β := λ r, r.val.2 in 
    begin
        have bij : bijective π₁ := bij_map_to_graph_fst f,
        
        let inv : 𝔸 → R := invrs π₁ bij,
        have elements : ∀ a , (π₂ ∘ inv) a = f a := 
            begin
                intro a,
                have inv_a : inv a = ⟨⟨a, f a⟩ , by tidy⟩ := 
                    bij.1 (by simp [invrs_id π₁ bij] : (π₁ ∘ inv) a = a),
                have π₂_r : π₂ ⟨⟨a, f a⟩ , by tidy⟩ = f a := rfl, 
                simp[inv_a , π₂_r]
            end,
        have f_π₂_inv : (π₂ ∘ inv) = f := funext elements,  
        split,
        intro hom,
        let ρ := (F.map inv) ∘ 𝔸.α ∘ π₁,
        use ρ,
        split,

        calc 𝔸.α ∘ π₁ = (𝟙 (F.obj 𝔸)) ∘ 𝔸.α ∘ π₁           : rfl
             ... = (F.map (𝟙 𝔸)) ∘ 𝔸.α ∘ π₁               : by rw ← (functor.map_id' F 𝔸)
             ... = (F.map (π₁ ⊚ inv)) ∘ 𝔸.α ∘ π₁         : by simp [invrs_id]
             ... = ((F.map π₁) ⊚ (F.map inv)) ∘ 𝔸.α ∘ π₁ : by rw functor.map_comp,
        
        calc Β.α ∘ (π₂)  = ((Β.α) ∘ f) ∘ π₁                         : by tidy
                ...      = ((F.map f) ∘ 𝔸.α) ∘ π₁                   : by rw ← (eq.symm hom)
                ...      = (F.map (π₂ ∘ inv)) ∘ 𝔸.α ∘ π₁            : by rw ← f_π₂_inv
                ...      = (F.map (π₂ ⊚ inv)) ∘ 𝔸.α ∘ π₁           : rfl
                ...      = ((F.map π₂) ⊚ (F.map inv)) ∘ 𝔸.α ∘ π₁   : by by rw functor.map_comp,

        intro bis,
        let ρ := some bis,
        let ℝ : Coalgebra F :=  ⟨R , ρ⟩,

        have hom_π := some_spec bis,
        let h_π₁ : ℝ ⟶ 𝔸 := ⟨π₁ , hom_π.1⟩,

        have hom_π₂_inv : is_coalgebra_homomorphism (π₂ ∘ inv) :=
            @comp_is_hom F 𝔸 ℝ Β 
            ⟨inv, bij_inverse_of_hom_is_hom h_π₁ bij⟩ ⟨π₂ , hom_π.2⟩,
            
        rw ← f_π₂_inv,
        
        exact hom_π₂_inv
    end

theorem shape_of_bisimulation :
    (Π (P : Coalgebra F) (ϕ₁ : P ⟶ 𝔸) (ϕ₂ : P ⟶ Β),
        let R : set (𝔸 × Β) := 
            λ ab : 𝔸 × Β , ∃ p ,ϕ₁ p = ab.1 ∧ ϕ₂ p = ab.2 in
        is_bisimulation R) 
    := 
    begin
        intros P ϕ₁ ϕ₂ R,
        let ϕ : P.carrier → R := λ p, 
            let ϕ_p : 𝔸 × Β := ⟨ϕ₁ p,  ϕ₂ p⟩ in
            have ϕ_p_R : ϕ_p ∈ R := exists.intro p
                ⟨(by simp : ϕ₁ p = ϕ_p.1), (by simp : ϕ₂ p = ϕ_p.2)⟩,
            ⟨ϕ_p,  ϕ_p_R⟩,
        have sur : surjective ϕ := λ r, by tidy,
        let μ : R → P := surj_inv sur,
        let ρ : R → F.obj R := (F.map ϕ) ∘ P.α ∘ μ,
        use ρ,
        let π₁ : R → 𝔸 := λ r, r.val.1,
        let π₂ : R → Β := λ r, r.val.2,
        have hom_ϕ₁ : 𝔸.α ∘ ϕ₁ = (F.map ϕ₁) ∘ P.α := ϕ₁.property,
        have hom_ϕ₂ : Β.α ∘ ϕ₂ = (F.map ϕ₂) ∘ P.α := ϕ₂.property,
        have inv_id : ϕ ∘ μ = @id R := funext (surj_inv_eq sur),

        have hom_π₁ : (F.map π₁) ∘ ρ = 𝔸.α ∘ π₁ := 
            calc (F.map π₁) ∘ ρ =  ((F.map π₁) ⊚ (F.map ϕ)) ∘ P.α ∘ μ : rfl 
                    ... = (F.map (π₁ ⊚ ϕ)) ∘ P.α ∘ μ              : by rw functor.map_comp
                    ... = ((F.map ϕ₁) ∘ P.α) ∘ μ                   : rfl
                    ... = 𝔸.α ∘ ϕ₁ ∘ μ                             : by rw ←hom_ϕ₁
                    ... = 𝔸.α ∘ π₁ ∘ ϕ ∘ μ                         : rfl
                    ... = 𝔸.α ∘ π₁ ∘ id                            : by rw inv_id,

        have hom_π₂ : (F.map π₂) ∘ ρ = Β.α ∘ π₂ := 
            calc (F.map π₂) ∘ ρ =  ((F.map π₂) ⊚ (F.map ϕ)) ∘ P.α ∘ μ   : rfl 
                    ... = (F.map (π₂ ⊚ ϕ)) ∘ P.α ∘ μ              : by rw functor.map_comp
                    ... = ((F.map ϕ₂) ∘ P.α) ∘ μ                   : rfl
                    ... = Β.α ∘ ϕ₂ ∘ μ                             : by rw ← hom_ϕ₂ 
                    ... = Β.α ∘ π₂ ∘ ϕ ∘ μ                         : rfl
                    ... = Β.α ∘ π₂ ∘ id                            : by rw inv_id,
        
        exact ⟨(eq.symm hom_π₁), (eq.symm hom_π₂)⟩
    end


end Bisimulation