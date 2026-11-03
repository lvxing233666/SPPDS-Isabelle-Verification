theory IOV_DIFC
  imports Main "HOL-Library.Multiset" "HOL-Library.List_Lexorder"
begin
declare [[goals_limit = 50]]
(* ========================================================================= *)
(* 1. Cryptographic Assumptions and Type Definitions*)
(* ========================================================================= *)

typedecl Data

type_synonym Name = string
type_synonym Attr = string
type_synonym Policy = "Attr set"
type_synonym DataName = string
type_synonym Nonce = string
type_synonym Tag = string
type_synonym Label = "Tag set"
type_synonym Result = bool
type_synonym DataKey = "Name × DataName"



axiomatization H :: "string ⇒ string" where
  H_inj: "inj H"
axiomatization Gen :: "Attr ⇒ Nonce"
axiomatization secure_combine :: "string ⇒ string ⇒ string" where
  secure_combine_inj: "inj (λ(u, r). secure_combine u r)"

definition sec_tag :: "DataName ⇒ Tag" where
  "sec_tag d = H d"

definition int_tag :: "DataName ⇒ string ⇒ Tag" where
  "int_tag d h = H (secure_combine d h)"


datatype Message =
    Msg_Policy_Req Name DataName Policy
  | Msg_Policy_Res Name DataName "string set" Nonce
  | Msg_Tag_Req_VP Name DataName "string set" 
  | Msg_Tag_Res_VP Name DataName "Tag set" "Tag set"               
  | Msg_Broadcast Name DataName Nonce                  
  | Msg_ID_Req_VR Name                           
  | Msg_ID_Res_TA Name string                                 
  | Msg_Tag_Req_VR string Name DataName "string set" 
  | Msg_Tag_Res_VR string Name DataName "Tag set" "Tag set"  
  | Msg_Data_Req string Name DataName Label Label 
  | Msg_Auth_Req string Name DataName Label Label Label Label      
  | Msg_Auth_Res string Name DataName bool            
  | Msg_Deliver string Name DataName Data


(* ========================================================================= *)
(*2. System State Definitions*)
(* ========================================================================= *)

record TA_State =
  registered_vehicles ::"(Name × (Attr set)) set"
  L_att :: "Attr ⇀ Nonce"
  id_records :: "string ⇀ (Name × Nonce)"
  obf_records :: "DataKey ⇀ (string set × Nonce)"

record RSU_State =
  hosted_data :: "DataKey ⇀ Data"
  hosted_labels :: "DataKey ⇀ (Label × Label)"

record Vehicle_State =
  vid :: Name
  v_attrs :: "Attr set"
  v_Ratts :: "Attr ⇀ Nonce"
  known_data :: "DataKey ⇀ Data"
  v_obf_sessions :: "DataName ⇀ (string set × Nonce)"

record Sys_State =
  ta :: TA_State
  rsu :: RSU_State
  vehicles :: "Name ⇀ Vehicle_State"
  net :: "Message multiset"

definition initial_state :: "Sys_State" where
  "initial_state =
   (| ta = (| registered_vehicles = {}, L_att = Map.empty, id_records = Map.empty, obf_records = Map.empty |),
      rsu = (| hosted_data = Map.empty, hosted_labels = Map.empty |),
      vehicles = Map.empty, 
      net = {#} |)"

(* ========================================================================= *)
(* 3. State Transition Rules *)
(* ========================================================================= *)

inductive transition :: "Sys_State ⇒ Sys_State ⇒ bool" where

  step0_vehicle_registration:
    "⟦ ATTR_v ≠ {};
       uid ∉ fst ` registered_vehicles (ta s); 
       (vehicles s) uid = None;
       new_Ratts = (λattr. if attr ∈ ATTR_v then Some (Gen attr) else None);
       s' = s(| ta := (ta s)(| registered_vehicles := registered_vehicles (ta s) ∪ {(uid, ATTR_v)},
                               L_att := L_att (ta s) ++ new_Ratts |),
               vehicles := (vehicles s)(uid ↦ (| vid = uid, 
                                              v_attrs = ATTR_v, 
                                              v_Ratts = new_Ratts, 
                                              known_data = Map.empty,
                                              v_obf_sessions = Map.empty |)) |) ⟧
     ⟹ transition s s'"

| step0_vp_generates_data:
    "⟦ (vehicles s) vp = Some vp_s;
       known_data vp_s (vp, dname) = None;
       vp_s' =
         vp_s(| known_data :=
                 (known_data vp_s)((vp, dname) ↦ data) |);
       s' =
         s(| vehicles := (vehicles s)(vp ↦ vp_s') |) ⟧
     ⟹ transition s s'"


| step1a_vp_requests_obfuscation:
    "⟦ (vehicles s) vp = Some vp_s;
       known_data vp_s (vp, dname) ≠ None;
       SP_attrs ⊆ v_attrs vp_s;
       SP_attrs ≠ {};
       s' = s(| net := net s + {#Msg_Policy_Req vp dname SP_attrs#} |) ⟧
     ⟹ transition s s'"


| step1b_ta_computes_obfuscation:
    "⟦ Msg_Policy_Req vp dname SP_attrs ∈# net s;
       ∀a∈SP_attrs. L_att (ta s) a ≠ None;
       obf_records (ta s) (vp, dname) = None;
       SP_prime =
         (λa. H (secure_combine (the (L_att (ta s) a)) r)) ` SP_attrs;
       s' = s(| ta := (ta s)(| obf_records :=
                                (obf_records (ta s))
                                  ((vp, dname) ↦ (SP_prime, r)) |),
                net :=
                  net s - {#Msg_Policy_Req vp dname SP_attrs#}
                  + {#Msg_Policy_Res vp dname SP_prime r#} |) ⟧
     ⟹ transition s s'"


| step1c_vp_stores_obfuscation:
    "⟦ Msg_Policy_Res vp dname SP_prime r ∈# net s;
       (vehicles s) vp = Some vp_s;
       vp_s' =
         vp_s(| v_obf_sessions :=
                  (v_obf_sessions vp_s)(dname ↦ (SP_prime, r)) |);
       s' = s(| vehicles := (vehicles s)(vp ↦ vp_s'),
               net := net s - {#Msg_Policy_Res vp dname SP_prime r#} |) ⟧
     ⟹ transition s s'"

| step2_vp_requests_tags:
    "⟦ (vehicles s) vp = Some vp_s;
       v_obf_sessions vp_s dname = Some (SP_prime, r);
       s' = s(| net := net s + {#Msg_Tag_Req_VP vp dname SP_prime#} |) ⟧
     ⟹ transition s s'"

| step3_rsu_computes_vp_tags:
    "⟦ Msg_Tag_Req_VP vp dname SP_prime ∈# net s;
       TagS_vp = {sec_tag dname};
       TagI_vp = (λh. int_tag dname h) ` SP_prime;
       s' = s(| net := net s - {#Msg_Tag_Req_VP vp dname SP_prime#}
                      + {#Msg_Tag_Res_VP vp dname TagS_vp TagI_vp#} |) ⟧
     ⟹ transition s s'"

| step4_5_vp_uploads:
    "⟦ Msg_Tag_Res_VP vp dname TagS_vp TagI_vp ∈# net s;
       (vehicles s) vp = Some vp_s;
       v_obf_sessions vp_s dname = Some (SP_prime, r);
       known_data vp_s (vp, dname) = Some data;
       hosted_data (rsu s) (vp, dname) = None;
       hosted_labels (rsu s) (vp, dname) = None;
       LS_vp = TagS_vp;
       LI_vp = TagI_vp;
       s' = s(| rsu := (rsu s)(| hosted_data :=
                                  (hosted_data (rsu s))((vp, dname) ↦ data),
                                 hosted_labels :=
                                  (hosted_labels (rsu s))((vp, dname) ↦ (LS_vp, LI_vp)) |),
               net := net s - {#Msg_Tag_Res_VP vp dname TagS_vp TagI_vp#}
                             + {#Msg_Broadcast vp dname r#} |) ⟧
     ⟹ transition s s'"

| step6a_vr_req_id:
    "⟦ Msg_Broadcast vp dname r ∈# net s;
       (vehicles s) vr = Some vr_s;
       s' = s(| net := net s + {#Msg_ID_Req_VR vr#} |) ⟧
     ⟹ transition s s'"

| step6b_ta_res_id:
    "⟦ Msg_ID_Req_VR vr ∈# net s;
       vr_id_prime = H (secure_combine vr R);
       id_records (ta s) vr_id_prime = None;
       s' = s(| ta := (ta s)(| id_records :=
                                (id_records (ta s))
                                  (vr_id_prime ↦ (vr, R)) |),
               net := net s - {#Msg_ID_Req_VR vr#}
                            + {#Msg_ID_Res_TA vr vr_id_prime#} |) ⟧
     ⟹ transition s s'"

| step6c_vr_requests_tags:
    "⟦ Msg_Broadcast vp dname r ∈# net s;
       Msg_ID_Res_TA vr vr_id_prime ∈# net s;
       (vehicles s) vr = Some vr_s;
       dom (v_Ratts vr_s) ≠ {};
       H_VR_set =
         (λa. H (secure_combine (the (v_Ratts vr_s a)) r))
         ` dom (v_Ratts vr_s);
       s' = s(| net := net s
                      - {#Msg_ID_Res_TA vr vr_id_prime#}
                      + {#Msg_Tag_Req_VR vr_id_prime vp dname H_VR_set#} |) ⟧
     ⟹ transition s s'"



| step7_rsu_computes_vr_tags:
    "⟦ Msg_Tag_Req_VR vr_id_prime vp dname H_VR_set ∈# net s;
       TagS_vr = {sec_tag dname};
       TagI_vr = (λh. int_tag dname h) ` H_VR_set;
       s' = s(| net := net s
                      - {#Msg_Tag_Req_VR vr_id_prime vp dname H_VR_set#}
                      + {#Msg_Tag_Res_VR vr_id_prime vp dname TagS_vr TagI_vr#} |) ⟧
     ⟹ transition s s'"

| step8_9_vr_requests_data:
    "⟦ Msg_Tag_Res_VR vr_id_prime vp dname TagS_vr TagI_vr ∈# net s;
       LS_vr = TagS_vr;
       LI_vr = TagI_vr;
       s' = s(| net := net s - {#Msg_Tag_Res_VR vr_id_prime vp dname TagS_vr TagI_vr#} 
                      + {#Msg_Data_Req vr_id_prime vp dname LS_vr LI_vr#} |) ⟧
     ⟹ transition s s'"

| step10_11_rsu_enforces_rules_and_forwards:
    "⟦ Msg_Data_Req vr_id_prime vp dname LS_vr LI_vr ∈# net s;
       hosted_labels (rsu s) (vp, dname) = Some (LS_data, LI_data);
       (vp, dname) ∈ dom (hosted_data (rsu s));
       LS_data ⊆ LS_vr;   
       LI_vr ⊆ LI_data;
       s' = s(| net := net s - {#Msg_Data_Req vr_id_prime vp dname LS_vr LI_vr#} 
                      + {#Msg_Auth_Req vr_id_prime vp dname 
                                      LS_data LI_data LS_vr LI_vr#} |) ⟧
     ⟹ transition s s'"

| step12_ta_verifies_access:
    "⟦ Msg_Auth_Req vr_id_prime vp dname 
                    LS_data LI_data LS_vr LI_vr ∈# net s;
       is_valid =
         (∃vr R_id attrs_vr SP_prime r H_VR_set.
             id_records (ta s) vr_id_prime = Some (vr, R_id) ∧
             vr_id_prime = H (secure_combine vr R_id) ∧
             (vr, attrs_vr) ∈ registered_vehicles (ta s) ∧
             obf_records (ta s) (vp, dname) = Some (SP_prime, r) ∧
             (∀a∈attrs_vr. L_att (ta s) a ≠ None) ∧
             H_VR_set =
               (λa. H (secure_combine (the (L_att (ta s) a)) r))
               ` attrs_vr ∧
             LS_data = {sec_tag dname} ∧
             LI_data = (λh. int_tag dname h) ` SP_prime ∧
             LS_vr = {sec_tag dname} ∧
             LI_vr = (λh. int_tag dname h) ` H_VR_set ∧
             LS_data ⊆ LS_vr ∧
             LI_vr ⊆ LI_data);
       s' = s(| net := net s 
                     - {#Msg_Auth_Req vr_id_prime vp dname 
                                      LS_data LI_data LS_vr LI_vr#} 
                     + {#Msg_Auth_Res vr_id_prime vp dname is_valid#} |) ⟧
     ⟹ transition s s'"


| step13_rsu_delivers:
    "⟦ Msg_Auth_Res vr_id_prime vp dname True ∈# net s;
       hosted_data (rsu s) (vp, dname) = Some data; 
       s' = s(| net := net s - {#Msg_Auth_Res vr_id_prime vp dname True#} 
                       + {#Msg_Deliver vr_id_prime vp dname data#} |) ⟧
     ⟹ transition s s'"

| vr_receives_data:
    "⟦ Msg_Deliver vr_id_prime vp dname data ∈# net s;
       id_records (ta s) vr_id_prime = Some (vr, R);
       (vehicles s) vr = Some vr_s;
       s' = s(| vehicles :=
                 (vehicles s)
                   (vr ↦ vr_s(| known_data :=
                                  (known_data vr_s)((vp, dname) ↦ data) |)),
               net := net s - {#Msg_Deliver vr_id_prime vp dname data#} |) ⟧
     ⟹ transition s s'"

(* ========================================================================= *)
(* 4. Trace and Global Invariant Definitions *)
(* ========================================================================= *)

inductive valid_trace :: "Sys_State list ⇒ bool" where
  base: "valid_trace [initial_state]"
| step: "valid_trace (s # tr) ⟹ transition s s' ⟹ valid_trace (s' # s # tr)"

definition system_consistency :: "Sys_State ⇒ bool" where
  "system_consistency s ⟷
  (∀vp dname LS_vp LI_vp. 
      hosted_labels (rsu s) (vp, dname) = 
        Some (LS_vp, LI_vp) ⟶ 
      LS_vp = {sec_tag dname} ∧ 
      (∃SP_prime. 
          LI_vp = (λh. int_tag dname h) ` SP_prime)) ∧

   (∀vp dname TagS_vp TagI_vp.
      Msg_Tag_Res_VP vp dname TagS_vp TagI_vp ∈# net s ⟶
      TagS_vp = {sec_tag dname} ∧
      (∃SP_prime. 
          TagI_vp = (λh. int_tag dname h) ` SP_prime))"


lemma msg_vp_diff_inv [dest]:
  "⟦ ∀d S I. Msg_Tag_Res_VP vp d S I ∈# net s ⟶ S = {sec_tag d} ∧ (∃P. I = (λh. int_tag d h) ` P);
     Msg_Tag_Res_VP vp d S I ∈# net s - X ⟧ 
  ⟹ S = {sec_tag d} ∧ (∃P. I = (λh. int_tag d h) ` P)"
  by (blast dest: in_diffD)

lemma consistency_initial: "system_consistency initial_state"
  apply (unfold initial_state_def system_consistency_def)
  apply auto
  done

lemma consistency_preserved:
  assumes "transition s s'" "system_consistency s"
  shows "system_consistency s'"
  using assms
  unfolding system_consistency_def
  apply (induct rule: transition.induct)
  apply (auto simp: fun_upd_apply dest: in_diffD)
  done

lemma hosted_labels_consistent:
  assumes "system_consistency s"
      and "hosted_labels (rsu s) (vp, dname) = Some (LS, LI)"
  shows "LS = {sec_tag dname} ∧
         (∃SP_prime. LI = (λh. int_tag dname h) ` SP_prime)"
  using assms
  unfolding system_consistency_def
  by blast

theorem data_confidentiality:
  assumes "transition s s'"
  shows "system_consistency s ⟹ 
         Msg_Auth_Req vr_id_prime vp dname LS_data LI_data LS_vr LI_vr ∈# net s' ⟹ 
         Msg_Auth_Req vr_id_prime vp dname LS_data LI_data LS_vr LI_vr ∉# net s ⟹
         ∃data SP_prime.
            hosted_data (rsu s) (vp, dname) = Some data ∧ 
            hosted_labels (rsu s) (vp, dname) =
              Some ({sec_tag dname}, (λh. int_tag dname h) ` SP_prime) ∧
            {sec_tag dname} ⊆ LS_vr ∧ 
            LI_vr ⊆ (λh. int_tag dname h) ` SP_prime ∧
            Msg_Data_Req vr_id_prime vp dname LS_vr LI_vr ∈# net s"
  using assms
  apply (induct rule: transition.induct)
  apply (auto dest: in_diffD)
  apply (metis hosted_labels_consistent singletonD)
  apply (metis hosted_labels_consistent singletonI)
  apply (metis hosted_labels_consistent subsetD singletonI)
  done

theorem data_integrity:
  assumes "transition s s'" "system_consistency s"
  shows "(∀vp dname TagS_vp TagI_vp.
            Msg_Tag_Res_VP vp dname TagS_vp TagI_vp ∈# net s' ⟶ 
            TagS_vp = {sec_tag dname} ∧
            (∃SP_prime.
               TagI_vp = (λh. int_tag dname h) ` SP_prime)) ∧
         (∀vp dname LS_vp LI_vp.
            hosted_labels (rsu s') (vp, dname) =
              Some (LS_vp, LI_vp) ⟶
            LS_vp = {sec_tag dname} ∧
            (∃SP_prime.
               LI_vp = (λh. int_tag dname h) ` SP_prime))"
  using consistency_preserved[OF assms]
  unfolding system_consistency_def
  apply auto
  done

theorem collusion_resistance:
  assumes "transition s s'"
  shows "Msg_Auth_Res vr_id_prime vp dname True ∈# net s' ⟹ 
         Msg_Auth_Res vr_id_prime vp dname True ∉# net s ⟹
         ∃vr R LS_data LI_data LS_vr LI_vr.
            Msg_Auth_Req vr_id_prime vp dname 
                         LS_data LI_data LS_vr LI_vr ∈# net s ∧
            id_records (ta s) vr_id_prime = Some (vr, R) ∧
            vr_id_prime = H (secure_combine vr R)"
  using assms
  apply (induct rule: transition.induct)
  apply (auto dest: in_diffD)
  done


theorem privacy_preserving:
  assumes "transition s s'"
  shows "Msg_Policy_Res vp dname SP_prime r ∈# net s' ⟹
         Msg_Policy_Res vp dname SP_prime r ∉# net s ⟹
         ∃SP_attrs.
           SP_prime =
             (λa. H (secure_combine
                    (the (L_att (ta s) a)) r)) ` SP_attrs"
  using assms
  apply (induct rule: transition.induct)
  apply (auto dest: in_diffD)
  done


end