|%
+$  granary-scry
  $-  ^
  (unit (unit *))
::
+$  index  @ud
+$  tnoun  $%([%atom p=@] [%cell (pair index index)])
+$  arena  (map * (pair tnoun index))  :: noun to [[ihead itail] inoun]
+$  ax-map  (map [s=index ax=@ud] [xi=index p=index path=(list ax-hint)])
+$  ax-hint
  $~  [%2 0 0]
  $%  [?(%2 %3) s=index p=index]
      [%cache s=index xi=index]
  ==
+$  cache  (map * phash)
+$  phash  @                     ::  Pedersen hash
:: +$  hash-req
::   $%  [%cell head=phash tail=phash]
::       [%atom val=@]
::   ==
::
+$  pred  [s=index f=index p=index]
+$  cairo-hint
  $%
      [%0 =pred path=index]
      [%1 =pred]
      [%2 =pred sf1=hints sf2=hints sf3=hints]
      [%3 =pred sf=hints]
      [%4 =pred sf=hints]
      [%5 =pred sf1=hints sf2=hints]
      [%6 =pred sf1=hints sf2=hints] :: got rid of the subf that doesn't get run...should be fine?
      [%7 =pred sf1=hints sf2=hints]
      [%8 =pred sf1=hints sf2=hints]
      [%9 =pred sf1=hints sf2=hints leaf=index path=index]
      [%10 =pred sf1=hints sf2=hints old-leaf=index path=index]
      [%11 =pred sf=hints (each [tag=index clue=hints] @)]
      :: [%12 (each [sf1=subf sf2=subf] phash)]
      [%jet =jet data=json] :: not every jet will return the whole sample as a noun
      [%cons =pred sf1=hints sf2=hints]
      [%invalid *] :: TODO: didn't want to deal with this [%invalid (each @ [@ phash])]
  ==
+$  hints  $@(~ [i=cairo-hint t=(list cairo-hint)]) :: TODO not sure if this needs to be a list
::  map of a noun's merkle children. root -> [left right]--
+$  jetmap  (map jet @ud)
::  Cost map of jets in stdlib
++  jets
  ^-  jetmap
  ::  TODO: determine *real* costs
  ::  these are totally made up placeholders
  %-  ~(gas by *jetmap)
  :~  
      :: ::  hoon
      ::  math
      [%$^%add 1]  [%$^%dec 1]  [%$^%div 1]
      [%$^%dvr 1]  [%$^%gte 1]  [%$^%gth 1]
      [%$^%lte 1]  [%$^%lth 1]  [%$^%max 1]
      [%$^%min 1]  [%$^%mod 1]  [%$^%mul 1]
      [%$^%sub 1]
      :: ???
      [%$^%cap 1]   [%$^%mas 1]    [%$^%peg 1]
      [%$^%need 1]  [%$^%fand 1]  [%$^%find 1]  [%$^%flop 1]
      [%$^%lent 1]  [%$^%levy 1]  [%$^%lien 1]  [%$^%murn 1]
      [%$^%oust 1]  [%$^%reap 1]  [%$^%rear 1]  [%$^%reel 1]
      [%$^%roll 1]  [%$^%scag 1]  [%$^%skid 1]  [%$^%skim 1]
      [%$^%skip 1]  [%$^%slag 1]  [%$^%snag 1]  [%$^%snip 1]
      [%$^%sort 1]  [%$^%spin 1]  [%$^%spun 1]  [%$^%turn 5]
      [%$^%weld 1]  [%$^%snap 1]  [%$^%into 1]  [%$^%welp 1]
      [%$^%zing 1]
      ::  bits
      [%$^%bex 1]  [%$^%can 1]  [%$^%cat 1]
      [%$^%cut 1]  [%$^%end 1]  [%$^%fil 1]
      [%$^%lsh 1]  [%$^%met 1]  [%$^%rap 1]
      [%$^%rep 1]  [%$^%rev 1]  [%$^%rip 1]
      [%$^%rsh 1]  [%$^%run 1]  [%$^%rut 1]
      [%$^%sew 1]  [%$^%swp 1]  [%$^%xeb 1]
      [%$^%con 1]  [%$^%dis 1]  [%$^%mix 1]
      ::  mug
      [%$^%pmug 1]  [%$^%aor 1]  [%$^%dor 1]
      [%$^%pgor 1]  [%$^%pmor 1]
      :: math
      [%$^%pow 1]  [%$^%sqt 1]
      ::  maps
      [%$^%all^%pin 1]  [%$^%any^%pin 1]  [%apt^%pin 1]
      [%$^%bif^%pin 1]  [%$^%del^%pin 1]  [%$^%dif^%pin 1]  [%$^%gas^%pin 1]
      [%$^%has^%pin 1]  [%$^%int^%pin 1]  [%$^%put^%pin 1]  [%$^%rep^%pin 1]
      [%$^%run^%pin 1]  [%tap^%pin 1]     [%$^%uni^%pin 1]  [%wyt^%pin 1]
      ::  sets
      [%$^%all^%pby 1]  [%$^%any^%pby 1]  [%$^%bif^%pby 1]  [%$^%del^%pby 1]
      [%$^%dif^%pby 1]  [%apt^%pby 1]     [%$^%gas^%pby 1]  [%$^%get^%pby 1]
      [%$^%has^%pby 1]  [%$^%int^%pby 1]  [%$^%jab^%pby 1]  [%$^%put^%pby 1]
      [%$^%rep^%pby 1]  [%$^%run^%pby 1]  [%tap^%pby 1]     [%$^%uni^%pby 1]
      [%$^%urn^%pby 1]  [%wyt^%pby 1]     [%key^%pby 1]
      :: ???
      [%$^%cu 1]   [%$^%jam 1]
      [%$^%mat 1]  [%$^%rub 1]
      ::  sha
      [%$^%sham 1.000]
      [%$^%shas 1.000]
      [%$^%shax 1.000]
      [%$^%shay 1.000]
      [%$^%shal 1.000]
      :: trip
      [%$^%trip 5]
      ::  auras
      [%$^%scot 5]  [%$^%scow 5]  [%$^%slaw 5]
      :: virtualization
      [%$^%mink 1]  [%$^%mole 1]  [%$^%mule 1]  [%$^%mure 1]
      [%$^%mute 1]  [%$^%slum 1]  [%$^%zock 1]  [%$^%zole 1]
      [%$^%zule 1]  [%$^%zure 1]  [%$^%zute 1]  [%$^%zlum 1]
      ::  smart-lib
      [%$^%pedersen-hash 10]  [%$^%keccak256^%keccak^%crypto 10]
      [%$^%ecdsa-raw-recover^%secp256k1^%secp^%crypto 10]
    ==
::
+$  jet
  $~  [%$ %add]
  $%  ::  hoon
      [%$ %add]       [%$ %dec]       [%$ %div]       [%$ %dvr]
      [%$ %gte]       [%$ %gth]       [%$ %lte]       [%$ %lth]
      [%$ %max]       [%$ %min]       [%$ %mod]       [%$ %mul]
      [%$ %sub]       [%$ %cap]       [%$ %mas]       [%$ %peg]
      [%$ %need]      [%$ %fand]      [%$ %find]      [%$ %flop]
      [%$ %lent]      [%$ %levy]      [%$ %lien]      [%$ %murn]
      [%$ %oust]      [%$ %reap]      [%$ %rear]      [%$ %reel]
      [%$ %roll]      [%$ %scag]      [%$ %skid]      [%$ %skim]
      [%$ %skip]      [%$ %slag]      [%$ %snag]      [%$ %snip]
      [%$ %sort]      [%$ %spin]      [%$ %spun]      [%$ %turn]
      [%$ %weld]      [%$ %snap]      [%$ %into]      [%$ %welp]
      [%$ %zing]      [%$ %bex]       [%$ %can]       [%$ %cat]
      [%$ %cut]       [%$ %end]       [%$ %fil]       [%$ %lsh]
      [%$ %met]       [%$ %rap]       [%$ %rep]       [%$ %rev]
      [%$ %rip]       [%$ %rsh]       [%$ %run]       [%$ %rut]
      [%$ %sew]       [%$ %swp]       [%$ %xeb]       [%$ %con]
      [%$ %dis]       [%$ %mix]       [%$ %pmug]      [%$ %aor]
      [%$ %dor]       [%$ %pgor]      [%$ %pmor]     [%$ %pow]
      [%$ %sqt]
      ::  set
      [%$ %all %pin]    [%$ %any %pin]    [%apt %pin]    [%$ %bif %pin]
      [%$ %del %pin]    [%$ %dif %pin]    [%$ %gas %pin]    [%$ %has %pin]
      [%$ %int %pin]    [%$ %put %pin]    [%$ %rep %pin]    [%$ %run %pin]
      [%tap %pin]       [%$ %uni %pin]    [%wyt %pin]
      ::  map
      [%$ %all %pby]    [%$ %any %pby]    [%$ %bif %pby]    [%$ %del %pby]
      [%$ %dif %pby]    [%apt %pby]       [%$ %gas %pby]    [%$ %get %pby]
      [%$ %has %pby]    [%$ %int %pby]    [%$ %jab %pby]    [%$ %put %pby]
      [%$ %rep %pby]    [%$ %run %pby]    [%tap %pby]       [%$ %uni %pby]
      [%$ %urn %pby]    [%wyt %pby]       [%key %pby]
      :: ??
      [%$ %cu]         [%$ %jam]        [%$ %mat]        [%$ %rub]
      :: %lug^%fl
      :: %drg^%fl    %add^%rd    %sub^%rd    %mul^%rd
      :: %div^%rd    %fma^%rd    %sqt^%rd    %lth^%rd
      :: %lte^%rd    %equ^%rd    %gte^%rd    %gth^%rd
      :: %add^%rs    %sub^%rs    %mul^%rs    %div^%rs
      :: %fma^%rs    %sqt^%rs    %lth^%rs    %lte^%rs
      :: %equ^%rs    %gte^%rs    %gth^%rs    %add^%rq
      :: %sub^%rq    %mul^%rq    %div^%rq    %fma^%rq
      :: %sqt^%rq    %lth^%rq    %lte^%rq    %equ^%rq
      :: %gte^%rq    %gth^%rq    %add^%rh    %sub^%rh
      :: %mul^%rh    %div^%rh    %fma^%rh    %sqt^%rh
      :: %lth^%rh    %lte^%rh    %equ^%rh    %gte^%rh
      :: %gth^%rh
      [%$ %sham]       [%$ %shas]       [%$ %shax]
      [%$ %shay]       [%$ %shal]       :: %raw^%og    %sha-1l
      :: %fein^%ob   %fynd^%ob   %ins^%po    %ind^%po
      :: %tos^%po    %tod^%po
      [%$ %trip]      ::  %fun^%bend
      :: %fun^%comp  %fun^%glue  %pfix       %plug
      :: %pose       %sfix       %fun^%cold  %fun^%cook
      :: %fun^%easy  %fun^%here  %fun^%just  %fun^%mask
      :: %fun^%shim  %fun^%stag  %stew       %fun^%tew
      ::  %fun^%stir  %fun^%stun  %nuck
      [%$ %scot]
      [%$ %scow]       [%$ %slaw]       [%$ %mink]       [%$ %mole]
      [%$ %mule]       [%$ %mure]       [%$ %mute]       [%$ %slum]
      [%$ %zock]       [%$ %zole]       [%$ %zule]       [%$ %zure]
      [%$ %zute]       [%$ %zlum]

      ::  smart-lib
      [%$ %pedersen-hash]          :: %$^%en^%ecba^%aes^%crypto
      :: %$^%de^%ecba^%aes^%crypto  %$^%en^%ecbb^%aes^%crypto
      :: %$^%de^%ecbb^%aes^%crypto  %$^%en^%ecbc^%aes^%crypto
      :: %$^%de^%ecbc^%aes^%crypto  %$^%en^%cbca^%aes^%crypto
      :: %$^%de^%cbca^%aes^%crypto  %$^%en^%cbcb^%aes^%crypto
      :: %$^%de^%cbcb^%aes^%crypto  %$^%en^%cbcc^%aes^%crypto
      :: %$^%de^%cbcc^%aes^%crypto  %$^%en^%ctra^%aes^%crypto
      :: %$^%en^%ctrb^%aes^%crypto  %$^%en^%ctrc^%aes^%crypto
      :: %$^%maca^%aes^%crypto      %$^%macb^%aes^%crypto
      :: %$^%macc^%aes^%crypto      %$^%s2va^%aes^%crypto
      :: %$^%s2vb^%aes^%crypto      %$^%s2vc^%aes^%crypto
      :: %$^%en^%siva^%aes^%crypto  %$^%de^%siva^%aes^%crypto
      :: %$^%en^%sivb^%aes^%crypto  %$^%de^%sivb^%aes^%crypto
      :: %$^%en^%sivc^%aes^%crypto  %$^%de^%sivc^%aes^%crypto
      :: %$^%point-add  %$^%scalarmult^%ed^%crypto
      :: %$^%scalarmult-base^%ed^%crypto
      :: %$^%add-scalarmult-scalarmult-base^%ed^%crypto
      :: %$^%add-double-scalarmult^%ed^%crypto
      :: %$^%puck^%ed^%crypto       %$^%shar^%ed^%crypto
      :: %$^%sign^%ed^%crypto       %$^%veri^%ed^%crypto
      :: %pbk^%scr       %pbl^%scr
      :: %hsh^%scr       %hsl^%scr
      :: %$^%keccak224^%keccak^%crypto
      [%$ %keccak256 %keccak %crypto]
      :: %$^%keccak384^%keccak^%crypto   %$^%keccak512^%keccak^%crypto
      :: %$ %hmac
      :: [%$ %make-k %secp256k1 %secp %crypto]
      :: %$^%ecdsa-raw-sign^%secp256k1^%secp^%crypto
      [%$ %ecdsa-raw-recover %secp256k1 %secp %crypto]
  ==
::
--
