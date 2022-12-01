
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

  let[@entry] main parameter storage =
  (* pair the payload with the current contract address, to ensure signatures
     can't be replayed accross different contracts if a key is reused. *)
  let ppl =
    let pact = match parameter.payload.action with
      | Transfer t -> ParamPair (ParamMutez t.amount, ParamKeyHash t.dest)
      | Delegate None -> ParamOption None
      | Delegate (Some kh) -> ParamOption (Some (ParamKeyHash kh))
      | Change_keys c -> ParamPair (ParamNat c.threshold', ParamList (List.map (fun k -> ParamKey k) c.keys'))
    in
    ParamPair (ParamNat parameter.payload.counter, pact)
  in
  let signature_target =
    Obj.pack
      (ParamPair (
        ppl,
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
  myassert (Nat.eq storage.stored_counter parameter.payload.counter) ;
  (* Compute the number of valid signatures *)
  let nsigs =
    Loop.left
      (fun (nsigs, keys, sigs) ->
        match keys, sigs with
        | [], [] -> Right nsigs
        | key :: keys, Some sig_ :: sigs ->
          (* Checks signatures, fails if invalid *)
          myassert (Crypto.check_signature key sig_ signature_target) ;
          Left (Nat.add nsigs (Nat 1), keys, sigs)
        | key :: keys, None :: sigs -> Left (nsigs, keys, sigs)
        (* tupleが本当に使えないか試してみる、無理なら *)
        | _ ->
            (*  There were fewer signatures in the list
                than keys. Not all signatures must be present, but
                they should be marked as absent using the option type.
            *)
            raise Fail)
      (Nat 0, storage.keys, parameter.sigs)
  in
  (*  Assert that the threshold is less than or equal to the
      number of valid signatures.
  *)
  myassert (Nat.le storage.threshold nsigs) ;

  (* Increment counter and place in storage *)
  (* XXX temp state is stored as a tuple.  Inefficient *)
  let storage =
    { stored_counter = Nat.add storage.stored_counter (Nat 1); threshold = storage.threshold; keys = storage.keys}
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
      [], {stored_counter = storage.stored_counter; threshold = threshold'; keys = keys'}

(*let parameter =
  { payload=  { counter= Nat 42
              ; action= Transfer { amount= Tz 1.0
                                ; dest= Contract.implicit_account (Key_hash "tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx")
                                }
              }

  ; sigs= [ Some (Signature "edsigtteMcYkviZ3rTaM6N7DWvgsyoTmEHGo91Q63qNJNYXFhTwWzmytanUj8G44aEZ8QDJt3myyxjuVwvRMikSJauZ96AvshWJ"); None ]
  }

let storage =
  { stored_counter= Nat 42
  ; threshold= Nat 1
  ; keys= [ Key "edpkuBknW28nW72KG6RoHtYW7p12T6GKc7nAbwYX5m8Wd9sDVC9yav" (* bootstrap1 *)
          ; Key "edpktzNbDAUjUk697W7gYg2CRuBQjyPxbEg8dLccYYwKSKvkPvjtV9" (* bootstrap2 *)
          ]
  }

let [@entry] test () () =
  let ops, _ = main parameter storage in
  ops, ()*)
