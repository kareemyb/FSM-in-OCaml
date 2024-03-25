open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q, 's) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  (* First, check if the symbol is not in the alphabet sigma *)
  match s with
  | Some sym when not (mem sym nfa.sigma) -> [] (* If not in sigma, return empty list *)
  | _ ->
      (* Collect states after applying the transition *)
      fold_left (fun acc q ->
          fold_left (fun acc_inner (source, symbol, target) ->
              if source = q && symbol = s then
                  if not (mem target acc_inner) then target :: acc_inner
                  else acc_inner
              else
                  acc_inner
          ) acc nfa.delta
      ) [] qs


let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
    (* Helper function to get the union of two lists without duplicates *)
    let union lst1 lst2 =
        fold_left (fun acc x -> if mem x acc then acc else x :: acc) lst1 lst2
    in

    (* Recursive function to compute e-closure *)
    let rec compute_closure current_qs =
        (* Find states that can be reached through epsilon transitions from current_qs *)
        let epsilon_reachable = move nfa current_qs None in
        (* Union of current states and epsilon-reachable states *)
        let new_qs = union current_qs epsilon_reachable in
        (* If no new states added, return, otherwise recurse *)
        if length new_qs = length current_qs then
            new_qs
        else
            compute_closure new_qs
    in

    compute_closure qs

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  (* Convert the string to a list of characters *)
  let chars = explode s in
  
  (* Start with the epsilon-closure of the initial state *)
  let start_states = e_closure nfa [nfa.q0] in
  
  (* Define a helper function to process each character of the string *)
  let rec process_states states = function
    | [] -> states (* Return the current states if string is empty *)
    | c::cs ->
      (* Compute the move on character c and then its epsilon-closure *)
      let next_states = e_closure nfa (move nfa states (Some c)) in
      process_states next_states cs
  in
  
  (* Compute the set of states the NFA could be in after reading the entire string *)
  let final_states = process_states start_states chars in
  
  (* Check if the resulting set of states intersects with the set of final states *)
  List.exists (fun q -> List.mem q nfa.fs) final_states



(*******************************)
(* Part 2: Subset Construction *)
(*******************************)
let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.map (fun s -> e_closure nfa (move nfa qs (Some s))) nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.combine (List.map (fun s -> Some s) nfa.sigma) (new_states nfa qs)
  |> List.map (fun (s, dest) -> (qs, s, dest))

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  if List.exists (fun q -> List.mem q nfa.fs) qs then [qs] else []

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  (* Step 1: Start with the ε-closure of the initial state of the NFA *)
  let start_state = e_closure nfa [nfa.q0] in
  
  let rec explore_states unexplored_states explored_states transitions finals =
    match unexplored_states with
    | [] -> (explored_states, transitions, finals)
    | current_state::rest ->
        (* If we've seen this state, continue with the rest *)
        if List.mem current_state explored_states then
          explore_states rest explored_states transitions finals
        else
          (* Step 2: Calculate transitions *)
          let current_transitions = new_trans nfa current_state in
          let next_states = new_states nfa current_state in
          
          (* Check if the current state is a final state *)
          let current_finals = new_finals nfa current_state in
          
          explore_states (rest @ next_states) 
                         (current_state :: explored_states)
                         (current_transitions @ transitions)
                         (current_finals @ finals)
  in
  
  let (dfa_states, dfa_transitions, dfa_finals) = explore_states [start_state] [] [] [] in
  
  (* Return the resulting DFA *)
  {
    sigma = nfa.sigma;
    qs = dfa_states;
    q0 = start_state;
    fs = dfa_finals;
    delta = dfa_transitions;
  }
