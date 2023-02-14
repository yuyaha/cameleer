type storage =
  { stored_counter : nat
  ; threshold : nat
  ; keys : key list
  }

type parameter =
  { payload : payload
  ; sigs : signature option list
  }

and payload =
  { counter : nat
  ; action : action
  }

and action =
  | Transfer of transfer
  | Delegate of key_hash option
  | Change_keys of change_keys

and transfer =
  { amount : tz
  ; dest : key_hash
  }

and change_keys =
  { threshold' : nat
  ; keys' : key list
  }

let [@logic] check signature_target = function
  (nsigs, keys, sigs) ->
    match keys, sigs with
    | [], [] -> Right (Ok nsigs)
    | key :: keys, Some sig_ :: sigs ->
      (* Checks signatures, fails if invalid *)
      if (Crypto.check_signature key sig_ signature_target)
          then Left (Nat.add nsigs (Nat 1), keys, sigs) else Right (Error "Assert_failure")
    | _ :: keys, None :: sigs -> Left (nsigs, keys, sigs)
    | _, _ -> Right (Error "Assert_failure")

let[@entry] main parameter storage =
  (* pair the payload with the current contract address, to ensure signatures
     can't be replayed accross different contracts if a key is reused. *)
  let signature_target =
    Obj.pack
      (ParamPair (
        ParamPair (
          ParamNat parameter.payload.counter,
          match parameter.payload.action with
          | Transfer t -> ParamOr (Left (ParamPair (ParamMutez t.amount, ParamKeyHash t.dest)))
          | Delegate None -> ParamOr (Right (ParamOr (Left (ParamOption None))))
          | Delegate (Some kh) -> ParamOr (Right (ParamOr (Left (ParamOption (Some (ParamKeyHash kh))))))
          | Change_keys c -> ParamOr (Right (ParamOr (Right (ParamPair (ParamNat c.threshold', ParamList (List.map (fun k -> ParamKey k) c.keys'))))))),
        ParamPair (
          ParamAddress
            (Contract.address
              (Contract.self
                (RepPair (
                  RepPair (
                    RepNat,
                    RepOr (
                      RepPair (
                        RepMutez,
                        RepContract),
                      RepOr (
                        RepOption RepKeyHash,
                        RepPair (
                            RepNat,
                            RepList RepKey)))),
                  RepList (RepOption RepSignature))))),
          (* This is always KT1BEqzn5Wx8uJrZNvuS9DVHmLvG9td3fDLi in the test *)
          ParamChainID (Chain_id "NetXdQprcVkpaWU"))))
  in
  (* Check that the counters *)
  if (Nat.eq storage.stored_counter parameter.payload.counter) then () else raise Assert_failure;
  (* Compute the number of valid signatures *)
  let nsigs =
    match Loop.left (check signature_target) (Nat 0, storage.keys, parameter.sigs) with
    | Ok nsigs -> nsigs
    | Error _ -> raise Assert_failure
  in
  (* Assert that the threshold is less than or equal to the number of valid signatures *)
  if (Nat.le storage.threshold nsigs) then () else raise Assert_failure;

  (* Increment counter and place in storage *)
  (* XXX temp state is stored as a tuple.  Inefficient *)
  let storage =
    { storage with stored_counter = Nat.add storage.stored_counter (Nat 1)}
  in

  (*  We have now handled the signature verification part,
      produce the operation requested by the signers.
  *)
  match parameter.payload.action with
  | Transfer {amount; dest} ->
      (* Transfer tokens *)
      ( [Operation.transfer_tokens (ParamUnit ()) amount (Contract.implicit_account dest)],
        storage )
  | Delegate key_hash_opt ->
      (* Change delegate *)
      [Operation.set_delegate key_hash_opt], storage
  | Change_keys {threshold'; keys'} ->
      (* Change set of signatures *)
      [], {storage with threshold = threshold'; keys = keys'}

(*@ ops, stg = main parameter storage
    ensures
      let signature_target =
        Obj.pack
          (ParamPair (
            ParamPair (
              ParamNat parameter.payload.counter,
              match parameter.payload.action with
          | Transfer t -> ParamOr (Left (ParamPair (ParamMutez t.amount, ParamKeyHash t.dest)))
          | Delegate None -> ParamOr (Right (ParamOr (Left (ParamOption None))))
          | Delegate (Some kh) -> ParamOr (Right (ParamOr (Left (ParamOption (Some (ParamKeyHash kh))))))
          | Change_keys c -> ParamOr (Right (ParamOr (Right (ParamPair (ParamNat c.threshold', ParamList (List.map (fun k -> ParamKey k) c.keys'))))))),
            ParamPair (
              ParamAddress
                (Contract.address
                  (Contract.self
                    (RepPair (
                      RepPair (
                        RepNat,
                        RepOr (
                          RepPair (
                            RepMutez,
                            RepContract),
                          RepOr (
                            RepOption RepKeyHash,
                            RepPair (
                                RepNat,
                                RepList RepKey)))),
                      RepList (RepOption RepSignature))))),
              ParamChainID (Chain_id "NetXdQprcVkpaWU"))))
      in
      if Nat.eq storage.stored_counter parameter.payload.counter then (
        match Loop.left (check signature_target) (Nat 0, storage.keys, parameter.sigs) with
        | Ok nsigs ->
          if Nat.le storage.threshold nsigs then (
            let storage = { storage with stored_counter = Nat.add storage.stored_counter (Nat 1)} in
            match parameter.payload.action with
            | Transfer {amount; dest} ->
              ops = Operation.transfer_tokens (ParamUnit ()) amount (Contract.implicit_account dest) :: []
              &&
              stg = storage
            | Delegate key_hash_opt ->
              ops = Operation.set_delegate key_hash_opt :: []
              &&
              stg = storage
            | Change_keys {threshold'; keys'} ->
              ops = []
              &&
              stg = { storage with threshold = threshold'; keys = keys' }
          ) else true
        | Error _ -> true
      ) else true
    raises
      Assert_failure ->
        not (Nat.eq storage.stored_counter parameter.payload.counter) ||
        let signature_target =
          Obj.pack
            (ParamPair (
              ParamPair (
                ParamNat parameter.payload.counter,
                match parameter.payload.action with
                | Transfer t -> ParamOr (Left (ParamPair (ParamMutez t.amount, ParamKeyHash t.dest)))
                | Delegate None -> ParamOr (Right (ParamOr (Left (ParamOption None))))
                | Delegate (Some kh) -> ParamOr (Right (ParamOr (Left (ParamOption (Some (ParamKeyHash kh))))))
                | Change_keys c -> ParamOr (Right (ParamOr (Right (ParamPair (ParamNat c.threshold', ParamList (List.map (fun k -> ParamKey k) c.keys'))))))),
              ParamPair (
                ParamAddress
                  (Contract.address
                    (Contract.self
                      (RepPair (
                        RepPair (
                          RepNat,
                          RepOr (
                            RepPair (
                              RepMutez,
                              RepContract),
                            RepOr (
                              RepOption RepKeyHash,
                              RepPair (
                                  RepNat,
                                  RepList RepKey)))),
                        RepList (RepOption RepSignature))))),
                ParamChainID (Chain_id "NetXdQprcVkpaWU"))))
        in
        match Loop.left (check signature_target) (Nat 0, storage.keys, parameter.sigs) with
        | Ok nsigs -> not (Nat.le storage.threshold nsigs)
        | Error _ -> true *)
