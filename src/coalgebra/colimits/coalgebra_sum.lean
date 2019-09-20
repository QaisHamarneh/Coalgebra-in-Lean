import category_theory.category
import category_theory.functor
import set_category.category_set
import coalgebra.Coalgebra
import set_category.colimits.Sum
import help_functions
import coalgebra.subcoalgebra


import tactic.tidy

universes u



namespace coalgebra_sum
open category_theory 
     set 
     coalgebra
     classical
     help_functions
     subcoalgebra
     Sum

local notation f ` ⊚ `:80 g:80 := category_struct.comp g f

variables   {A B C: Type u} 
            {F : Type u ⥤ Type u}
            (𝔸 : Coalgebra F)
            (Β : Coalgebra F)

open sum

def α_sum 
    : (𝔸 ⊕ Β) → F.obj (𝔸 ⊕ Β)
    | (inl a) := ((F.map inl) ∘ 𝔸.α) a
    | (inr b) := ((F.map inr) ∘ Β.α) b
 

def sum_of_coalgebras 
            : Coalgebra F  :=
            ⟨(𝔸 ⊕ Β) ,  (α_sum 𝔸 Β)⟩

lemma inl_is_homomorphism : 
    @is_coalgebra_homomorphism F 𝔸 (sum_of_coalgebras 𝔸 Β) inl
    := by {dsimp at *, refl}

lemma inr_is_homomorphism :
    @is_coalgebra_homomorphism F Β (sum_of_coalgebras 𝔸 Β) inr
    := by {dsimp at *, refl}

infix ` ⊞ ` :20 := sum_of_coalgebras

theorem set_sum_is_coalgebra_sum : 
    let e₁ : 𝔸 → (𝔸 ⊕ Β) := inl in
    let e₂ : Β → (𝔸 ⊕ Β) := inr in
    let h_e₁ : 𝔸 ⟶ (𝔸 ⊞ Β) := ⟨e₁ ,  inl_is_homomorphism 𝔸 Β⟩ in
    let h_e₂ : Β ⟶ (𝔸 ⊞ Β) := ⟨e₂ ,  inr_is_homomorphism 𝔸 Β⟩ in
            is_sum (𝔸 ⊞ Β) h_e₁ h_e₂
        := 
    begin
        intros e₁ e₂ h_e₁ h_e₂ ℚ ϕ₁ ϕ₂,
        
        let σ : 𝔸 ⊕ Β ⟶ ℚ := 
            some (disjoint_union_is_sum ℚ ϕ₁ ϕ₂),

        let γ := ℚ.α,
        let α :=  (𝔸 ⊞ Β).α,

        let hom_inl : 
            α ∘ inl = (F.map inl) ∘ 𝔸.α := 
                inl_is_homomorphism 𝔸 Β,
        let hom_inr : 
            α ∘ inr = (F.map inr) ∘ Β.α 
                := inr_is_homomorphism 𝔸 Β,

        let hom_ϕ₁ : γ ∘ ϕ₁.val =  (F.map ϕ₁.val) ∘ 𝔸.α := ϕ₁.property,
        let hom_ϕ₂ : γ ∘ ϕ₂.val =  (F.map ϕ₂.val) ∘ Β.α := ϕ₂.property,

        have h0 : _ := 
            some_spec (disjoint_union_is_sum ℚ ϕ₁ ϕ₂),

        have h1 : ϕ₁.val = σ ∘ inl ∧ ϕ₂.val = σ ∘ inr:= 
            and.left h0,

        have h2 : γ ∘ σ ∘ inl = (F.map σ) ∘ α ∘ inl := 
            calc 
             γ ∘ (σ ∘ inl) = γ ∘ ϕ₁.val                    : by rw [and.left h1]
                ...      = (F.map ϕ₁.val) ∘ 𝔸.α               : by rw [hom_ϕ₁]
                ...      = (F.map (σ ∘ inl)) ∘ 𝔸.α        : by rw [and.left h1]
                ...      = (F.map (σ ⊚ inl)) ∘ 𝔸.α        : by simp
                ...  = ((F.map σ) ⊚ (F.map inl)) ∘ 𝔸.α    : by rw ← functor.map_comp
                ...      = (F.map σ) ∘ (F.map inl) ∘ 𝔸.α   : by simp
                ...      = (F.map σ) ∘ α ∘ inl             : by rw [hom_inl],
        have h3 : γ ∘ σ ∘ inr = (F.map σ) ∘ α ∘ inr := 
            calc γ ∘ (σ ∘ inr) = γ ∘ ϕ₂.val                      : by rw [and.right h1]
                     ...      = (F.map ϕ₂.val) ∘ Β.α             : by rw [hom_ϕ₂]
                     ...      = (F.map (σ ∘ inr)) ∘ Β.α          : by rw [and.right h1]
                     ...      = (F.map (σ ⊚ inr)) ∘ Β.α        : by simp
                     ...  = ((F.map σ) ⊚ (F.map inr)) ∘ Β.α    : by rw ← functor.map_comp
                     ...      = (F.map σ) ∘ (F.map inr) ∘ Β.α   : by simp
                     ...      = (F.map σ) ∘ α ∘ inr             : by rw [hom_inr],
        have h4 : ∀ ab : 𝔸 ⊕ Β, (γ ∘ σ) ab = ((F.map σ) ∘ α) ab := 
                begin 
                    intro ab,
                    induction ab,
                    case inl :  { 
                                    show (γ ∘ σ ∘ inl) ab = ((F.map σ) ∘ α ∘ inl) ab,
                                    by rw h2
                                },
                    case inr :  { 
                                    show (γ ∘ σ ∘ inr) ab = ((F.map σ) ∘ α ∘ inr) ab,
                                    by rw h3
                                },
                end,
        
        
        have h5 : @is_coalgebra_homomorphism F
                (𝔸 ⊞ Β) ℚ σ
                  := funext h4,
        
        let ex_uni : 
            ∃! s , ϕ₁.val = s ∘ inl ∧ ϕ₂.val = s ∘ inr := 
            disjoint_union_is_sum ℚ ϕ₁ ϕ₂,
        
        let ex : 
            ∃ s , 
                (ϕ₁.val = s ∘ inl ∧ ϕ₂.val = s ∘ inr)
                ∧ @is_coalgebra_homomorphism F
                    (𝔸 ⊞ Β) ℚ s := 
                        exists.intro σ 
                        (and.intro h1 h5),
        let s := some ex,
        have spec_s : (ϕ₁.val = s ∘ inl ∧ ϕ₂.val = s ∘ inr) ∧ 
                    @is_coalgebra_homomorphism F (𝔸 ⊞ Β) ℚ s
            := some_spec ex,
        use s,
        exact spec_s.2,
        split,
        exact ⟨eq_in_set.1 spec_s.1.1,
            eq_in_set.1 spec_s.1.2⟩,
        let s₁ := some ex_uni,
        have spec_s₁ : _ := some_spec ex_uni,
        have s₁_s : s₁ = s := eq.symm (spec_s₁.2 s spec_s.1),
        intros s₂ spec_s₂,

        have s₂_s₁ : s₂.val = s₁ :=  spec_s₁.2 s₂
            ⟨eq_in_set.2 spec_s₂.1, eq_in_set.2 spec_s₂.2⟩,
        
        have s₂_s : s₂.val = s := by simp [s₁_s, s₂_s₁],

        exact eq_in_set.1 s₂_s


    end



noncomputable theorem subcoalgebra_union_is_coalgebra 
    {U₁ U₂ : set 𝔸}
    (S₁ : SubCoalgebra U₁)
    (S₂ : SubCoalgebra U₂) 
    : SubCoalgebra (U₁ ∪ U₂) := 
    begin

        let S : Coalgebra F := ⟨U₁ , S₁.α⟩ ⊞ ⟨U₂ , S₂.α⟩,
        
        have ex := set_sum_is_coalgebra_sum ⟨U₁ , S₁.α⟩ ⟨U₂ , S₂.α⟩ 𝔸 
                     ⟨ (U₁↪ 𝔸), S₁.h⟩  ⟨(U₂ ↪ 𝔸) , S₂.h⟩,

        let ϕ : S ⟶ 𝔸 := some ex,

        have spec : (((U₁↪ 𝔸) = ϕ ∘ inl ∧ (U₂ ↪ 𝔸) = ϕ ∘ inr))
            := ⟨ eq_in_set.2 (some_spec ex).1.1,
                 eq_in_set.2 (some_spec ex).1.2 ⟩ ,

        have all : ∀ a : 𝔸 , a ∈ (range ϕ) ↔ a ∈ (U₁ ∪ U₂) :=
            λ a,
            iff.intro
            begin
                assume ar : a ∈ range ϕ,
                cases (mem_range.1 ar) with s ϕs_a,
                induction s,
                case inl : 
                    begin 
                        have h01 : (ϕ ∘ inl) s ∈ U₁ := 
                            spec.1 ▸ s.property,
                        have h02 : a ∈ U₁ := ϕs_a ▸ h01,
                        by simp [h02],
                    end,
                case inr : 
                    begin 
                        have h01 : (ϕ ∘ inr) s ∈ U₂ := 
                            spec.2 ▸ s.property,
                        have h02 : a ∈ U₂ :=  (ϕs_a ▸ h01),
                        by simp [h02], 
                    end,
            end
            begin
                assume auu : a ∈ U₁ ∨ a ∈ U₂,
                apply or.elim auu,
                assume au1: a ∈ U₁,
                have h01 : a = (ϕ ∘ inl) ⟨a , au1⟩  :=
                    spec.1 ▸ rfl,
                exact exists.intro (inl ⟨a , au1⟩) (eq.symm (h01)),
                assume au2: a ∈ U₂,
                have h01 : a = (ϕ ∘ inr) ⟨a , au2⟩  :=
                    spec.2 ▸ rfl,
                exact exists.intro (inr ⟨a , au2⟩) (eq.symm h01)
            end,

        rw ←(eq_sets.1 all), 
        exact range_is_subCoalgebra ϕ,
        
    end

















-- def pw (U V : set 𝔸) 
--     [∀ x , decidable (x ∈ U ∩ V)]
--         (w : U ∩ V)
--     :U → U ∩ V := λ u , if uUV : u.val ∈ U ∩ V
--                     then ⟨u.val , uUV⟩ 
--                     else ⟨w.val , w.property⟩

-- def qw (U V : set 𝔸) 
--     [∀ x , decidable (x ∈ V)]
--         (w : U ∩ V)
--     :𝔸 → V := λ a , if aV : a ∈ V 
--                     then ⟨a , aV⟩ 
--                     else ⟨w.val , and.right w.property⟩

theorem subcoalgebra_intersection_is_coalgebra 
    {U V : set 𝔸}
    (S₁ : SubCoalgebra U)
    (S₂ : SubCoalgebra V) 
    [∀ x : 𝔸 , decidable (x ∈ U ∩ V)]
    [∀ x : 𝔸 , decidable (x ∈ V)]
    : openset (U ∩ V) := 
    begin
        let I : set 𝔸 := U ∩ V,
        cases classical.em (nonempty (I)) with n_emp emp,
        
        let w : ↥I := choice n_emp ,
        
        let incV : I → V := set.inclusion (by simp),
        let incU : I → U := set.inclusion (by simp),

        let p_w :U → U ∩ V := λ u , if uUV : u.val ∈ U ∩ V
                    then ⟨u.val , uUV⟩ 
                    else ⟨w.val , w.property⟩,
        let q_w :𝔸 → V := λ a , if aV : a ∈ V 
                    then ⟨a , aV⟩ 
                    else ⟨w.val , and.right w.property⟩,

        have h1 : ∀ u:U ,
            (incV ∘ p_w) u = (q_w ∘ (U ↪ 𝔸)) u := 
            assume u, 
            @by_cases (u.val ∈ I)  ((incV ∘ p_w) u = (q_w ∘ (U ↪ 𝔸)) u)
                begin 
                    intro uI,
                    have pwu_u : p_w u = ⟨u.val , uI⟩:= 
                        by simp [p_w , rfl, uI],
                    have qwu_u: (q_w) u.val = 
                                    (⟨u.val , uI.2⟩ : V)  := 
                        by simp [q_w, rfl, uI.2],
                    calc (incV ∘ p_w) u 
                                = incV  ⟨u.val , uI⟩  : by rw ←pwu_u
                            ... = (⟨u.val , uI.2⟩: V) : rfl
                            ... = q_w u.val          : by rw ←qwu_u
                end 
                begin 
                    intro uNI,
                    have pwu_w : p_w u = w := by simp [p_w , uNI, rfl],
                    have qwu_u: q_w u.val = 
                                    (⟨w.val , (w.property).2⟩ : V)  := 
                        begin
                            simp[q_w],
                            split_ifs,
                            exact absurd (and.intro u.property h) uNI,
                            exact rfl
                        end,
                    calc incV (p_w u)
                                = incV w                      : by rw pwu_w
                            ... = (⟨w.val , w.property.2⟩: V)  : rfl
                            ... = q_w u.val                   : by rw ←qwu_u
                           
                
                end 
            ,
        have h11 : incV ∘ p_w = q_w ∘ (U ↪ 𝔸) :=
            funext h1,
        
        have h22 : q_w  ∘ (V ↪ 𝔸) = id := 
            funext (by {dsimp at *,  simp [q_w]}),

        let γ := (F.map p_w) ∘ S₁.α ∘ incU,

        have hom_eq : (F.map (I ↪ 𝔸)) ∘ γ = 𝔸.α ∘ (I ↪ 𝔸) := 
            calc (F.map ((V ↪ 𝔸) ⊚ incV)) ∘ (F.map p_w) ∘ S₁.α ∘ incU 
                    = ((F.map (V ↪ 𝔸)) ⊚ (F.map incV)) ∘ (F.map p_w) ∘ S₁.α ∘ incU : by rw functor.map_comp
                ... = (F.map (V ↪ 𝔸)) ∘ ((F.map incV) ⊚ (F.map p_w)) ∘ S₁.α ∘ incU : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (incV ⊚ p_w)) ∘ S₁.α ∘ incU : by rw ←functor.map_comp
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (incV ∘ p_w)) ∘ S₁.α ∘ incU : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (q_w ∘ (U ↪ 𝔸))) ∘ S₁.α ∘ incU : by rw ←h11
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (q_w ⊚ (U ↪ 𝔸))) ∘ S₁.α ∘ incU : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ ((F.map q_w) ⊚ ((F.map (U ↪ 𝔸)))) ∘ S₁.α ∘ incU : by rw functor.map_comp
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map q_w) ∘ ((F.map (U ↪ 𝔸)) ∘ S₁.α) ∘ incU : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map q_w) ∘ 𝔸.α ∘ (U ↪ 𝔸) ∘ incU : by rw  eq.symm S₁.h
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map q_w) ∘ (𝔸.α ∘ (V ↪ 𝔸)) ∘ incV : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map q_w) ∘ (F.map (V ↪ 𝔸)) ∘ S₂.α ∘ incV : by rw ← (eq.symm S₂.h)
                ... = (F.map (V ↪ 𝔸)) ∘ ((F.map q_w) ⊚ (F.map (V ↪ 𝔸))) ∘ S₂.α ∘ incV : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (q_w ⊚ (V ↪ 𝔸))) ∘ S₂.α ∘ incV : by rw ←functor.map_comp
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (q_w ∘ (V ↪ 𝔸))) ∘ S₂.α ∘ incV : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map id) ∘ S₂.α ∘ incV : by rw h22
                ... = (F.map (V ↪ 𝔸)) ∘ (F.map (𝟙 V)) ∘ S₂.α ∘ incV : rfl
                ... = (F.map (V ↪ 𝔸)) ∘ (𝟙 (F.obj V)) ∘ S₂.α ∘ incV : by rw functor.map_id'
                ... = ((F.map (V ↪ 𝔸)) ∘ S₂.α) ∘ incV : rfl
                ... = 𝔸.α ∘ (V ↪ 𝔸) ∘ incV : by rw eq.symm S₂.h,

        exact exists.intro γ (eq.symm hom_eq),
        
        exact empty_openset emp
    end

end coalgebra_sum
