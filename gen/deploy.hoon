/+  smart=zig-sys-smart
:-  %say
|=  [[now=@da eny=@uvJ bek=beak] [cont=path ~] ~]
^-  *
=/  text  .^(@t %cx (weld /(scot %p p.bek)/zig/(scot %da now) cont))
=/  smart-txt  .^(@t %cx /(scot %p p.bek)/zig/(scot %da now)/lib/zig/sys/smart/hoon)
=/  hoon-txt  .^(@t %cx /(scot %p p.bek)/zig/(scot %da now)/lib/zig/sys/tiny/hoon)
=/  hoe  (slap !>(~) (ream hoon-txt))
=/  hoed  (slap hoe (ream smart-txt))
=/  contract  (slap hoed (ream text))
:-  %noun
q:(slap contract (ream '-'))