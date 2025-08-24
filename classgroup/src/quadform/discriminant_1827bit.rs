use std::{ str::FromStr, sync::LazyLock };

use rug::Integer;
use serde::{ Deserialize, Serialize };

use crate::quadform::{ QuadForm, TrDiscriminant };

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct Delta1827bit {}

impl TrDiscriminant for Delta1827bit {
    // $$\Delta_k = -pq$$.
    fn Delta_k() -> &'static Integer {
        static DELTA_K: LazyLock<Integer> = LazyLock::new(
            || -(Delta1827bit::p().clone() * Delta1827bit::q())
        );
        return &DELTA_K;
    }

    // $$\Delta_p = p^2 \Delta_K$$.
    fn Delta_p() -> &'static Integer {
        static DELTA_P: LazyLock<Integer> = LazyLock::new(
            || Delta1827bit::p().clone().square() * Delta1827bit::Delta_k()
        );
        &DELTA_P
    }

    // The parameter $$p$$ is
    // * secp256k1 curve order;
    // * conductor of class group;
    // * the exact order of ideal class $$f$$.
    fn p() -> &'static Integer {
        static P: LazyLock<Integer> = LazyLock::new(|| {
            let digits =
                "115792089237316195423570985008687907852837564279074904382605163141518161494337";
            let res = Integer::from_str(&digits).unwrap();
            res
        });
        return &P;
    }

    fn q() -> &'static Integer {
        static Q: LazyLock<Integer> = LazyLock::new(|| {
            let digits =
                String::new() +
                "48474472628700222923600969375027378087116755912885" +
                "87788495719189273446748546445177624419173867057605" +
                "51016463948293585828503413171858012696345486012888" +
                "32514770523674044351404340503270850746146295547003" +
                "64356098056533837497119748587811197297927778529919" +
                "23912450015197293099774936765720942209602972662597" +
                "73135110240079006671204851235107353298185846649703" +
                "90531374794858383583283696733028838887186219054732" +
                "73726378383329304439900099298658002101894316845131" +
                "75995537260100115381365951108406182362250863655200" +
                "39481895959255506876183366040440174295566297882006" +
                "7822065312853937663";
            let res = Integer::from_str(&digits).unwrap();
            res
        });
        return &Q;
    }

    fn identity() -> &'static QuadForm<Self> where Self: Sized + Clone {
        static ID: LazyLock<QuadForm<Delta1827bit>> = LazyLock::new(||
            QuadForm::new(1, 1).unwrap()
        );
        return &ID;
    }

    fn f() -> &'static QuadForm<Self> where Self: Sized + Clone {
        static F: LazyLock<QuadForm<Delta1827bit>> = LazyLock::new(|| {
            let a = Delta1827bit::p().clone().square();
            let b = Delta1827bit::p().clone();
            QuadForm::new(a, b).unwrap()
        });
        return &F;
    }

    fn generator() -> &'static QuadForm<Self> where Self: Sized + Clone {
        static G: LazyLock<QuadForm<Delta1827bit>> = LazyLock::new(|| {
            // g.a
            let digits =
                String::new() +
                "33799333618379597504442812678860818344767515871521" +
                "91195702130129876229099797314884670653751744957540" +
                "13708310221036914571883142408342121304069845236338" +
                "72990658260905666145505091041715961939407084528014" +
                "46727936908797340323098201338663853170233065328696" +
                "85679008242206927509296739979441372389551408836395" +
                "14583749367508061843954725442677806535751234616550" +
                "52057240595359404437943529185106860238910043016082";
            let a = Integer::from_str(&digits).unwrap();

            // g.b
            let digits =
                String::new() +
                "58358596530709071629230628954813789065094567413901" +
                "15173250460405445996130246571504137037236495025406" +
                "20524141771755836193445321542771727610998914641435" +
                "83046235404103174114873829883081661462607082144282" +
                "56894699546993136617207192803136225253872135816913" +
                "76433867317288963211366773277788622600301760076870" +
                "15790858390775199286445826383171957023481318023285" +
                "705914617463624817890014105071550499557399120835";
            let b = Integer::from_str(&digits).unwrap();

            QuadForm::new(a, b).unwrap()
        });
        return &G;
    }

    fn L() -> &'static Integer {
        static L: LazyLock<Integer> = LazyLock::new(|| {
            let mut val = Delta1827bit::Delta_p().clone().abs();
            val /= 4;
            val = val.sqrt();
            val = val.sqrt();
            val
        });
        return &L;
    }

    // This is the estimated upper bound of |G|, which is denoted as
    // $$\tilde s$$ in some research papers, e.g. [CL15].
    fn order_g() -> &'static Integer {
        static ORDER_G: LazyLock<Integer> = LazyLock::new(|| {
            let digits =
                String::new() +
                "70874029964003222178994413383062782755071292199599" +
                "73297684376464648879140029924517335736762241468971" +
                "59046777641756836926990886237520223776483585568680" +
                "28456505343659927114861398173913787770528036913753" +
                "91771478429036676214714932549995049179049799644100" +
                "63027828233706155968124702241849857898213763251030" +
                "06605987671787325355230432";
            let res = Integer::from_str(&digits).unwrap();
            res
        });
        return &ORDER_G;
    }
}
