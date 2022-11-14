/+  smart=zig-sys-smart
|%
+$  state-0
  $:  ::  the addresses we share with others
      mapping=(map town=@ux [=address:smart proof=(unit proof)])
      ::  the addresses we've received
      known=(map ship (map town=@ux [=address:smart proof=(unit proof)]))
  ==
::
+$  proof
  [=sig:smart =message]
::
+$  message
  $:  msg=@t  ::  'Uqbar Address Attestation'
      =ship
      town=@ux
      date=@da
  ==
++  domain  ^-  id:smart  `@`'share-address-agent'
::
++  message-json
  ^-  json
  %-  need
  %-  de-json:html
  '''
  [
    {"msg": "t"},
    {"ship": "p"},
    {"town": "ux"},
    {"date": "da"}
  ]
  '''
::
::  pokes
::
+$  action
  $%  ::  poke self
      [%set-address town=@ux =address:smart make-proof=?]
      ::  poked by others
      [%get-address town=@ux]
      ::  received in kind
      [%none-found from=ship town=@ux]
      [%got-address from=ship town=@ux =address:smart proof=(unit proof)]
  ==
::
::  peeks
::
--