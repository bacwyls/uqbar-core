::  share-address [UQ| DAO]:
::
::  A simple agent for ships to broadcast the address they're using on Uqbar.
::
/-  *zig-share-address, w=zig-wallet
/+  agentio,
    dbug,
    default-agent,
    verb,
    smart=zig-sys-smart
::
|%
+$  card  card:agent:gall
--
::
=|  state-0
=*  state  -
::
%-  agent:dbug
%+  verb  |
^-  agent:gall
|_  =bowl:gall
+*  this  .
    def   ~(. (default-agent this %|) bowl)
    io    ~(. agentio bowl)
::
++  on-init  `this(mapping ~, known ~)
++  on-save  !>(state)
++  on-load
  |=  old=vase
  `this(state !<(state-0 old))
::
++  on-poke
  |=  [=mark =vase]
  ^-  (quip card _this)
  ?.  ?=(%share-address-action mark)  (on-poke:def mark vase)
  =/  act=action  !<(action vase)
  ::
  ?-    -.act
      %set-address
    ?>  =(src.bowl our.bowl)
    ?.  make-proof.act
      `this(mapping (~(put by mapping) town.act [address.act ~]))
    ::  poke wallet to produce typed-message
    ::  watch for poke-ack to scry and set sig in proof
    =/  =message
      :^  'Uqbar Address Attestation'
      our.bowl  town.act  now.bowl
    =/  =typed-message:smart
      [domain `@ux`(sham message-json) message]
    :_  %=    this
            mapping
          (~(put by mapping) town.act [address.act `[[0 0 0] message]])
        ==
    :_  ~
    =+  :~  %poke-for-sig
            (scot %ux town.act)
            (scot %ux address.act)
            (scot %ux `@ux`(sham typed-message))
        ==
    %+  ~(poke pass:io -)
      [our.bowl %wallet]
    :-  %wallet-poke
    !>  ^-  wallet-poke:w
    :^    %sign-typed-message
        address.act
      domain
    [message-json message]
  ::
      %get-address
    ::  poke sender back with %got-address if we have one
    :_  this  :_  ~
    %+  ~(poke pass:io /share-address-poke)
      [src.bowl %share-address]
    :-  %share-address-poke
    !>  ^-  action
    ?~  found=(~(get by mapping) town.act)
      [%none-found our.bowl town.act]
    [%got-address our.bowl town.act u.found]
  ::
      %none-found
    ?>  =(src.bowl from.act)
    ~&  >>>  "%share-address: {<src.bowl>} failed to share"
    `this
  ::
      %got-address
    ?>  =(src.bowl from.act)
    ~&  >  "%share-address: got address {<address.act>} from {<src.bowl>}"
    =/  known-ship=(map @ux [address:smart (unit proof)])
      %+  ~(put by (~(gut by known) from.act ~))
      town.act  [address.act proof.act]
    ::  verify proof, if any
    ?~  proof.act
      `this(known (~(put by known) from.act known-ship))
    =/  =typed-message:smart
      [domain `@ux`(sham message-json) message.u.proof.act]
    ?>  =((recover:smart typed-message sig.u.proof.act) address.act)
    `this(known (~(put by known) from.act known-ship))
  ==
::
++  on-agent
  |=  [=wire =sign:agent:gall]
  ^-  (quip card _this)
  ?+    wire  (on-agent:def wire sign)
      [%poke-for-sig @ @ @ ~]
    ?.  ?=(%poke-ack -.sign)  `this
    ?^  p.sign
      ::  failure to sign
      ~&  >>>  "%share-address: wallet failed to give signed message"
      `this
    ::  success, scry for message hash and set state
    =/  town-id  (slav %ux i.t.wire)
    =/  address  (slav %ux i.t.t.wire)
    =/  hash     (slav %ux i.t.t.t.wire)
    =/  upd=wallet-update:w
      .^  wallet-update:w  %gx
          (scry:io %wallet /signed-message/[i.t.t.t.wire]/noun)
      ==
    ?>  ?=(%signed-message -.upd)
    :-  ~
    %=    this
        mapping
      %+  ~(jab by mapping)  town-id
      |=  [=address:smart proof=(unit proof)]
      [address `[sig.upd message:(need proof)]]
    ==
  ==
::
++  on-arvo  on-arvo:def
++  on-watch  on-watch:def
++  on-leave  on-leave:def
++  on-peek   on-peek:def
++  on-fail   on-fail:def
--
