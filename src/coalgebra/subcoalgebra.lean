import set_category.category_set
import coalgebra.Coalgebra
import help_functions

universe u


namespace subcoalgebra

open category_theory set category_set coalgebra function classical
    help_functions

variables {F : Type u ⥤ Type u}
        {𝔸 Β ℂ : Coalgebra F}

/--
    Openset is a prop that checks if there exists 
    a coalgebra structure α : S → F(S), such that 
    The inclusion from ⟨S, α⟩ to 𝔸 is a homomorphism
-/
def openset {𝔸 : Coalgebra F} (S : set 𝔸) : Prop :=
    ∃ α : S → F.obj S , 
        @is_coalgebra_homomorphism 
            F
            ⟨S , α⟩
            𝔸
            (S ↪ 𝔸)


/--
    The structure SubCoalgebra from the set S ⊆ 𝔸
    consists of α : S → F(S) and a proof h, that 
    the inclusion from ⟨S, α⟩ is a homomorphism
-/
structure SubCoalgebra (S : set 𝔸)  :=
    (α : S → F.obj S) 
    (h: @is_coalgebra_homomorphism F
                            ⟨S , α⟩ 
                            𝔸 
                            (S ↪ 𝔸))

noncomputable def openset_to_subcoalgebra {S : set 𝔸} (o : openset S):
    SubCoalgebra S :=
    ⟨some o, some_spec o⟩ 


instance SubCoalgebra_is_Coalgebra (S : set 𝔸): 
    has_coe (SubCoalgebra S) (Coalgebra F)
    := ⟨λ Sub , ⟨S , Sub.α⟩ ⟩ 


lemma subcoalgebra_unique_structure
            (S : set 𝔸)
            (h : openset S)
            : let α := some h in
            ∀ σ : S → F.obj S, 
                    @is_coalgebra_homomorphism F
                        ⟨S , σ⟩
                        𝔸 
                        (S ↪ 𝔸) → 
                    σ = α 
            := 
    begin 
        intros α σ h0,
        let coS : SubCoalgebra S := ⟨α , (some_spec h)⟩,
        cases classical.em (nonempty S) with nonemp emp,
        
        haveI inh : inhabited S := nonemptyInhabited nonemp,
        have hom : @is_coalgebra_homomorphism F
                            coS 𝔸 (S ↪ 𝔸) := some_spec h,
        have h2 : (F.map (S ↪ 𝔸)) ∘ α = (F.map (S ↪ 𝔸)) ∘ σ :=
                calc (F.map (S ↪ 𝔸)) ∘ α
                        = 𝔸.α ∘ (S ↪ 𝔸)          : eq.symm hom
                    ... = (F.map (S ↪ 𝔸)) ∘ σ    : h0,
        haveI h3 : mono (F.map (S ↪ 𝔸)) :=
            mono_preserving_functor (S ↪ 𝔸) (inj_inclusion 𝔸 S),

        exact eq.symm (left_cancel (F.map (S ↪ 𝔸)) h2),

        have h2 : ∀ (f₁ f₂ : S → F.obj S), f₁ = f₂ := 
            map_from_empty S (F.obj S) (nonempty_notexists emp),
        exact h2 σ (some h)
    end 

lemma surj_hom_to_coStructure
    (ϕ : homomorphism 𝔸 Β)
    (sur : surjective ϕ)
    : 
    let χ : Β → F.obj Β := λ b, 
        ((F.map ϕ) ∘ 𝔸.α) (some (sur b)) in 
    Β.α = χ := 
    begin
        intro χ,
        have elements : ∀ b, Β.α b= χ b := 
        begin
            intro b,
            let a := some (sur b),
            have a_b : ϕ a = b := some_spec (sur b),
            have χ_b : χ b = ((F.map ϕ) ∘ 𝔸.α) a := rfl,
            have hom_ϕ : Β.α ∘ ϕ = (F.map ϕ) ∘ 𝔸.α := ϕ.property,
            have h_ϕ : ∀ a, Β.α (ϕ a) = ((F.map ϕ) ∘ 𝔸.α) a := 
                λ a , 
                have h1 : (Β.α ∘ ϕ) a = ((F.map ϕ) ∘ 𝔸.α) a := 
                    by rw hom_ϕ,
                h1,
            have α_a : Β.α b = ((F.map ϕ) ∘ 𝔸.α) a := 
                a_b ▸ (h_ϕ a),
            rw α_a,
        end,
        exact funext elements
    end


def congruence 
    (ϕ : homomorphism 𝔸 Β) 
    :  𝔸 → 𝔸 → Prop := kern ϕ

def congruence2 (h: ∃ ϕ : 𝔸 → Β , is_coalgebra_homomorphism ϕ)
    : 𝔸 → 𝔸 → Prop :=  kern (some h)


def homomorphic_image (𝔸 Β: Coalgebra F) : Prop := 
    ∃ ϕ : homomorphism 𝔸 Β, surjective ϕ




def decompose (f: homomorphism 𝔸 Β)
    : f.val = ((range f) ↪ Β) ∘ range_factorization f
    := rfl

lemma structure_existance 
    (ϕ : homomorphism 𝔸 Β) 
    : ∃ α : (range ϕ) → F.obj (range ϕ), 
        let ℝ : Coalgebra F :=⟨range ϕ , α⟩ in 
        @is_coalgebra_homomorphism F 𝔸 ℝ
                (range_factorization ϕ) ∧ 
        @is_coalgebra_homomorphism F ℝ Β
                ((range ϕ) ↪ Β) := 
    begin
        have ex : _ := Factorization
                        ϕ 
                        (range_factorization ϕ)
                        ((range ϕ) ↪ Β)
                        (decompose ϕ)
                        ((epi_iff_surjective (range_factorization ϕ)).2 
                            surjective_onto_range)
                        (inj_inclusion Β (range ϕ)),
        cases ex with α hom,
        exact 
            exists.intro α hom.left
    end

def homomorphic_image_of_range 
    (ϕ : homomorphism 𝔸 Β) [inhabited 𝔸]
        : ∃ α : (range ϕ) → F.obj (range ϕ), 
        homomorphic_image 𝔸 ⟨range ϕ , α⟩  :=
        begin
            have ex : _ := structure_existance ϕ,
            cases ex with α hom
            ,
            let coalg : Coalgebra F:= ⟨range ϕ , α⟩ 
            ,
            have h : homomorphic_image 𝔸 coalg :=
                have x : true := trivial,
                exists.intro
                ⟨range_factorization ϕ ,  hom.left⟩
                surjective_onto_range,
            exact exists.intro α h
        end

noncomputable lemma range_is_subCoalgebra (ϕ : homomorphism 𝔸 Β) 
    : SubCoalgebra (range ϕ) :=  
        have ex : _ := structure_existance ϕ,
        let α : (range ϕ) → F.obj (range ϕ) := some ex in
        ⟨α , (some_spec ex).right⟩ 





noncomputable
lemma empty_is_Subcoalgebra (𝔸 : Coalgebra F) : SubCoalgebra (∅ : set 𝔸) :=
{
    α := empty_map (∅ : set 𝔸) not_nonempty_empty (F.obj (∅ : set 𝔸)),
    h := by tidy
} 

lemma empty_is_openset (𝔸 : Coalgebra F) : openset (∅ : set 𝔸) :=
    begin
        let α := empty_map (∅ : set 𝔸) not_nonempty_empty (F.obj (∅ : set 𝔸)),
        use α,
        tidy
    end

lemma empty_openset {S: set 𝔸} (emp : ¬ nonempty S): openset S :=
    begin
        let α : S → F.obj S := empty_map S emp (F.obj S),
        use α,
        exact empty_hom_dom (inclusion S) emp
    end

def is_largest_coalgebra {S : set 𝔸} (P : set S): Prop :=
    (∃ α : P → F.obj P , 
        @is_coalgebra_homomorphism F ⟨P, α⟩ 𝔸 
                        ((S ↪ 𝔸) ∘ (P ↪ S))) ∧ 
        ∀ P₁ : set S, 
    (∃ α : P₁ → F.obj P₁ , 
    @is_coalgebra_homomorphism F ⟨P₁, α⟩ 𝔸 
                    ((S ↪ 𝔸) ∘ (P₁ ↪ S))) → P₁ ⊆ P

noncomputable def largest_Coalgebra {S : set 𝔸} {P : set S} 
                        (lar : is_largest_coalgebra P):
    Coalgebra F := ⟨P , some lar.1⟩ 

-- lemma largest_subcoalgebra_exists (S : set 𝔸) :
--     ∃ P ⊆ S, is_largest_subcoalgebra S P H := 
--         begin
--             let emp : set 𝔸 := ∅,
--             have h : emp ⊆ S := by tidy,
--             use emp,
--             use h,
--             split,
--             exact empty_is_openset 𝔸,
--             intros p h op,
            
--         end

-- def largest_subcoalgebra_set (S : set 𝔸):
--     set 𝔸 := some (largest_subcoalgebra_exists S)

-- noncomputable def largest_subcoalgebra (S : set 𝔸): 
--     SubCoalgebra (largest_subcoalgebra_set S) :=
--     begin
--         let P : set 𝔸 := some (largest_subcoalgebra_exists S),
--         have op : openset P := (some_spec (some_spec (largest_subcoalgebra_exists S))).1,

--         let α : P → F.obj P := some op,
--         have hom : _ := some_spec op,

--         exact ⟨α ,hom⟩ 
--     end





















end subcoalgebra