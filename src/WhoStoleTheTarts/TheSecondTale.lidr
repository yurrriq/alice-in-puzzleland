= The Second Tale

> module WhoStoleTheTarts.TheSecondTale
>
> %access export
> %default total

This time, someone stole the flour!
<blockquote>
Find the miscreant, and take his head off!
</blockquote>

== Suspects

We know it was one of the March Hare, the Mad Hatter and the Dormouse.

> data MarchHare
>
> data MadHatter
>
> data Dormouse
>
> SomeoneStoleTheFlour : Type
> SomeoneStoleTheFlour = Either (    MarchHare, Not MadHatter, Not Dormouse)
>                      $ Either (Not MarchHare,     MadHatter, Not Dormouse)
>                               (Not MarchHare, Not MadHatter,     Dormouse)

== Statements

The March Hare claims the Hatter stole it.

> MarchHareStatement : (truth : Bool) -> Type
> MarchHareStatement False = Not MadHatter
> MarchHareStatement True = (Not MarchHare, MadHatter, Not Dormouse)

The thief told the truth...

> MadHatterStatement : (truth : Bool) -> Type
> MadHatterStatement False = Not MadHatter
> MadHatterStatement True = (Not MarchHare, MadHatter, Not Dormouse)

> DormouseStatement : (truth : Bool) -> Type
> DormouseStatement False = Not Dormouse
> DormouseStatement True = (Not MarchHare, Not MadHatter, Dormouse)

== Revelation

... and is the only one who did.

> Revelation : Type
> Revelation = Either ( (MarchHareStatement True, MarchHare)
>                     , MadHatterStatement False
>                     , DormouseStatement  False )
>                     ( Either ( MarchHareStatement False
>                              , MadHatterStatement True
>                              , DormouseStatement  False )
>                              ( MarchHareStatement False
>                              , MadHatterStatement False
>                              , DormouseStatement  True ) )

== Conclusion

> lemma1 : SomeoneStoleTheFlour
>       -> (Not MarchHare, Not MadHatter)
>       -> Dormouse
> lemma1 (Left (marchHare, _)) (toBlame, _)
>   = absurd (toBlame marchHare)
> lemma1 (Right (Left (_, madHatter, _))) (_, toBlame)
>   = absurd (toBlame madHatter)
> lemma1 (Right (Right (it, was, dormouse))) obviously
>   = dormouse

Given the [statements](#statements) above and the [revelation](#revelation),

> Thief : SomeoneStoleTheFlour -> Revelation

... we can conclude the Dormouse stole the flour.

>      -> (Not MarchHare, Not MadHatter, Dormouse)

Let's assume the March Hare did it. If so, then they told the truth, which would
mean that the Hatter stole the flour. They couldn't both have done it, so the
March Hare must have lied, which means they and the Mad Hatter are innocent.

> Thief (Left marchHare) (Left (((_, madHatter, _), _), toBlame, _))
>   = absurd (toBlame madHatter)
> Thief (Right (Left (toBlame, _))) (Left ((_, marchHare), _))
>   = absurd (toBlame marchHare)

If it was neither the March Hare nor the Mad Hatter,
then it must've been the Dormouse.

> Thief someone (Right (Left (notHatter, (notMarchHare, _), _)))
>   = let dormouse = lemma1 someone (notMarchHare, notHatter) in
>     (notMarchHare, notHatter, dormouse)
> Thief (Right (Right dormouse)) _ = dormouse

If the Dormouse told the truth,
then they stole the flour.

> Thief _ (Right (Right (_, _, dormouse))) = dormouse

∎
