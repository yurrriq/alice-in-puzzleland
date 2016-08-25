= Who Stole the Tarts?

> module WhoStoleTheTarts
>
> %access  export
> %default total


== The First Tale

> namespace TheFirstTale
>  %hide Prelude.Pairs.DPair.fst

=== Suspects

>   data MarchHare
>   data MadHatter
>   data Dormouse
>
>   SomeoneStoleTheJam : Type
>   SomeoneStoleTheJam = Either (    MarchHare, Not MadHatter, Not Dormouse)
>                      $ Either (Not MarchHare,     MadHatter, Not Dormouse)
>                               (Not MarchHare, Not MadHatter,     Dormouse)

=== Statements

\begin{quote}
I never stole the jam!
\end{quote}

>   MarchHareStatement : (truth : Bool) -> Type
>   MarchHareStatement False = MarchHare
>   MarchHareStatement True  = Not MarchHare

\begin{quote}
One of us stole it, but it wasn't me!
\end{quote}

>   MadHatterStatement : (truth : Bool) -> Type
>   MadHatterStatement False = (MadHatter, Not MarchHare, Not Dormouse)
>   MadHatterStatement True  = (Not MadHatter, Either MarchHare Dormouse)

\begin{quote}
At least one of them [spoke the truth].
\end{quote}

>   DormouseStatement : (truth : Bool) -> Type
>   DormouseStatement False = (MarchHareStatement False, MadHatterStatement False)
>   DormouseStatement True  = Not (MarchHareStatement False, MadHatterStatement False)


=== Revelation

>   Revelation : Type

The March Hare and the Dormouse were not both speaking the truth, i.e.
either the March Hare spoke the truth and the Dormouse did not

>   Revelation = Either (MarchHareStatement True,  DormouseStatement False)

or the March Hare did not speak the truth and the Dormouse did.

>                       (MarchHareStatement False, DormouseStatement True)


=== Conclusion

The March Hare stole the jam.

>   Thief : SomeoneStoleTheJam -> Revelation
>        -> (MarchHare, Not MadHatter, Not Dormouse)
>   Thief (Left marchHare) _ = marchHare
>   Thief _ (Left (itWas, (marchHare,_))) = absurd (itWas marchHare)
>   Thief (Left (_,did,it)) (Right (marchHare,_)) = (marchHare,did,it)
>   Thief (Right (Left (itWas,_))) (Right (him,_)) = absurd (itWas him)
>   Thief (Right (Right (itWas,_))) (Left (_,(him,_))) = absurd (itWas him)
>   Thief (Right (Right (itWas,_))) (Right (him,_)) = absurd (itWas him)
