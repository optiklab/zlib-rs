use crate::Code;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::fixed_tree_specs;

// These native-used blocks keep both positive proofs and bad-cell counterexamples small.
macro_rules! fixed_literal_block {
    ($name:ident, $base:literal, [$($cell:expr),* $(,)?]) => {
        #[cfg_attr(verus_keep_ghost, cfg_eval)]
        #[cfg_attr(verus_keep_ghost, verus_spec(result =>
            ensures result@ == Seq::new(16, |index: int|
                fixed_tree_specs::literal_entry(($base as int) + index)),
        ))]
        const fn $name() -> [Code; 16] {
            let table = [$($cell),*];
            #[cfg(verus_keep_ghost)]
            proof! {
                let produced = table@;
                let expected = Seq::new(16, |index: int|
                    fixed_tree_specs::literal_entry(($base as int) + index));
                assert(produced[0] == fixed_tree_specs::literal_entry(($base as int) + 0)) by (compute);
                assert(produced[1] == fixed_tree_specs::literal_entry(($base as int) + 1)) by (compute);
                assert(produced[2] == fixed_tree_specs::literal_entry(($base as int) + 2)) by (compute);
                assert(produced[3] == fixed_tree_specs::literal_entry(($base as int) + 3)) by (compute);
                assert(produced[4] == fixed_tree_specs::literal_entry(($base as int) + 4)) by (compute);
                assert(produced[5] == fixed_tree_specs::literal_entry(($base as int) + 5)) by (compute);
                assert(produced[6] == fixed_tree_specs::literal_entry(($base as int) + 6)) by (compute);
                assert(produced[7] == fixed_tree_specs::literal_entry(($base as int) + 7)) by (compute);
                assert(produced[8] == fixed_tree_specs::literal_entry(($base as int) + 8)) by (compute);
                assert(produced[9] == fixed_tree_specs::literal_entry(($base as int) + 9)) by (compute);
                assert(produced[10] == fixed_tree_specs::literal_entry(($base as int) + 10)) by (compute);
                assert(produced[11] == fixed_tree_specs::literal_entry(($base as int) + 11)) by (compute);
                assert(produced[12] == fixed_tree_specs::literal_entry(($base as int) + 12)) by (compute);
                assert(produced[13] == fixed_tree_specs::literal_entry(($base as int) + 13)) by (compute);
                assert(produced[14] == fixed_tree_specs::literal_entry(($base as int) + 14)) by (compute);
                assert(produced[15] == fixed_tree_specs::literal_entry(($base as int) + 15)) by (compute);
                assert(produced =~= expected);
            }
            table
        }
    };
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (Code { op, bits, val }),
))]
const fn code(op: u8, bits: u8, val: u16) -> Code {
    Code { op, bits, val }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::root_table_specs::table(crate::huffman_specs::Alphabet::Distances,
            crate::fixed_tree_specs::distance_lengths(), 5, result@),
        forall|index: int| 0 <= index < 32 ==>
            #[trigger] result@[index] == crate::fixed_tree_specs::distance_entry(index),
))]
pub(crate) fn fixed_distance_table() -> &'static [Code; 32] {
    let table = &DISTFIX;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::fixed_tree_proofs::distance_table(table@);
    }
    table
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::root_table_specs::table(crate::huffman_specs::Alphabet::LiteralLengths,
            crate::fixed_tree_specs::literal_lengths(), 9, result@),
        forall|index: int| 0 <= index < 512 ==>
            #[trigger] result@[index] == crate::fixed_tree_specs::literal_entry(index),
))]
pub(crate) fn fixed_literal_table() -> &'static [Code; 512] {
    let table = &LENFIX;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::fixed_tree_proofs::literal_table(table@);
    }
    table
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures forall|index: int| 0 <= index < 512 ==>
        #[trigger] LENFIX@[index] == crate::fixed_tree_specs::literal_entry(index),
))]
pub(crate) const LENFIX: [Code; 512] = build_fixed_literal_table();

fixed_literal_block!(
    fixed_literal_000,
    0,
    [
        code(96, 7, 0),
        code(0, 8, 80),
        code(0, 8, 16),
        code(20, 8, 115),
        code(18, 7, 31),
        code(0, 8, 112),
        code(0, 8, 48),
        code(0, 9, 192),
        code(16, 7, 10),
        code(0, 8, 96),
        code(0, 8, 32),
        code(0, 9, 160),
        code(0, 8, 0),
        code(0, 8, 128),
        code(0, 8, 64),
        code(0, 9, 224),
    ]
);
fixed_literal_block!(
    fixed_literal_016,
    16,
    [
        code(16, 7, 6),
        code(0, 8, 88),
        code(0, 8, 24),
        code(0, 9, 144),
        code(19, 7, 59),
        code(0, 8, 120),
        code(0, 8, 56),
        code(0, 9, 208),
        code(17, 7, 17),
        code(0, 8, 104),
        code(0, 8, 40),
        code(0, 9, 176),
        code(0, 8, 8),
        code(0, 8, 136),
        code(0, 8, 72),
        code(0, 9, 240),
    ]
);
fixed_literal_block!(
    fixed_literal_032,
    32,
    [
        code(16, 7, 4),
        code(0, 8, 84),
        code(0, 8, 20),
        code(21, 8, 227),
        code(19, 7, 43),
        code(0, 8, 116),
        code(0, 8, 52),
        code(0, 9, 200),
        code(17, 7, 13),
        code(0, 8, 100),
        code(0, 8, 36),
        code(0, 9, 168),
        code(0, 8, 4),
        code(0, 8, 132),
        code(0, 8, 68),
        code(0, 9, 232),
    ]
);
fixed_literal_block!(
    fixed_literal_048,
    48,
    [
        code(16, 7, 8),
        code(0, 8, 92),
        code(0, 8, 28),
        code(0, 9, 152),
        code(20, 7, 83),
        code(0, 8, 124),
        code(0, 8, 60),
        code(0, 9, 216),
        code(18, 7, 23),
        code(0, 8, 108),
        code(0, 8, 44),
        code(0, 9, 184),
        code(0, 8, 12),
        code(0, 8, 140),
        code(0, 8, 76),
        code(0, 9, 248),
    ]
);
fixed_literal_block!(
    fixed_literal_064,
    64,
    [
        code(16, 7, 3),
        code(0, 8, 82),
        code(0, 8, 18),
        code(21, 8, 163),
        code(19, 7, 35),
        code(0, 8, 114),
        code(0, 8, 50),
        code(0, 9, 196),
        code(17, 7, 11),
        code(0, 8, 98),
        code(0, 8, 34),
        code(0, 9, 164),
        code(0, 8, 2),
        code(0, 8, 130),
        code(0, 8, 66),
        code(0, 9, 228),
    ]
);
fixed_literal_block!(
    fixed_literal_080,
    80,
    [
        code(16, 7, 7),
        code(0, 8, 90),
        code(0, 8, 26),
        code(0, 9, 148),
        code(20, 7, 67),
        code(0, 8, 122),
        code(0, 8, 58),
        code(0, 9, 212),
        code(18, 7, 19),
        code(0, 8, 106),
        code(0, 8, 42),
        code(0, 9, 180),
        code(0, 8, 10),
        code(0, 8, 138),
        code(0, 8, 74),
        code(0, 9, 244),
    ]
);
fixed_literal_block!(
    fixed_literal_096,
    96,
    [
        code(16, 7, 5),
        code(0, 8, 86),
        code(0, 8, 22),
        code(64, 8, 0),
        code(19, 7, 51),
        code(0, 8, 118),
        code(0, 8, 54),
        code(0, 9, 204),
        code(17, 7, 15),
        code(0, 8, 102),
        code(0, 8, 38),
        code(0, 9, 172),
        code(0, 8, 6),
        code(0, 8, 134),
        code(0, 8, 70),
        code(0, 9, 236),
    ]
);
fixed_literal_block!(
    fixed_literal_112,
    112,
    [
        code(16, 7, 9),
        code(0, 8, 94),
        code(0, 8, 30),
        code(0, 9, 156),
        code(20, 7, 99),
        code(0, 8, 126),
        code(0, 8, 62),
        code(0, 9, 220),
        code(18, 7, 27),
        code(0, 8, 110),
        code(0, 8, 46),
        code(0, 9, 188),
        code(0, 8, 14),
        code(0, 8, 142),
        code(0, 8, 78),
        code(0, 9, 252),
    ]
);
fixed_literal_block!(
    fixed_literal_128,
    128,
    [
        code(96, 7, 0),
        code(0, 8, 81),
        code(0, 8, 17),
        code(21, 8, 131),
        code(18, 7, 31),
        code(0, 8, 113),
        code(0, 8, 49),
        code(0, 9, 194),
        code(16, 7, 10),
        code(0, 8, 97),
        code(0, 8, 33),
        code(0, 9, 162),
        code(0, 8, 1),
        code(0, 8, 129),
        code(0, 8, 65),
        code(0, 9, 226),
    ]
);
fixed_literal_block!(
    fixed_literal_144,
    144,
    [
        code(16, 7, 6),
        code(0, 8, 89),
        code(0, 8, 25),
        code(0, 9, 146),
        code(19, 7, 59),
        code(0, 8, 121),
        code(0, 8, 57),
        code(0, 9, 210),
        code(17, 7, 17),
        code(0, 8, 105),
        code(0, 8, 41),
        code(0, 9, 178),
        code(0, 8, 9),
        code(0, 8, 137),
        code(0, 8, 73),
        code(0, 9, 242),
    ]
);
fixed_literal_block!(
    fixed_literal_160,
    160,
    [
        code(16, 7, 4),
        code(0, 8, 85),
        code(0, 8, 21),
        code(16, 8, 258),
        code(19, 7, 43),
        code(0, 8, 117),
        code(0, 8, 53),
        code(0, 9, 202),
        code(17, 7, 13),
        code(0, 8, 101),
        code(0, 8, 37),
        code(0, 9, 170),
        code(0, 8, 5),
        code(0, 8, 133),
        code(0, 8, 69),
        code(0, 9, 234),
    ]
);
fixed_literal_block!(
    fixed_literal_176,
    176,
    [
        code(16, 7, 8),
        code(0, 8, 93),
        code(0, 8, 29),
        code(0, 9, 154),
        code(20, 7, 83),
        code(0, 8, 125),
        code(0, 8, 61),
        code(0, 9, 218),
        code(18, 7, 23),
        code(0, 8, 109),
        code(0, 8, 45),
        code(0, 9, 186),
        code(0, 8, 13),
        code(0, 8, 141),
        code(0, 8, 77),
        code(0, 9, 250),
    ]
);
fixed_literal_block!(
    fixed_literal_192,
    192,
    [
        code(16, 7, 3),
        code(0, 8, 83),
        code(0, 8, 19),
        code(21, 8, 195),
        code(19, 7, 35),
        code(0, 8, 115),
        code(0, 8, 51),
        code(0, 9, 198),
        code(17, 7, 11),
        code(0, 8, 99),
        code(0, 8, 35),
        code(0, 9, 166),
        code(0, 8, 3),
        code(0, 8, 131),
        code(0, 8, 67),
        code(0, 9, 230),
    ]
);
fixed_literal_block!(
    fixed_literal_208,
    208,
    [
        code(16, 7, 7),
        code(0, 8, 91),
        code(0, 8, 27),
        code(0, 9, 150),
        code(20, 7, 67),
        code(0, 8, 123),
        code(0, 8, 59),
        code(0, 9, 214),
        code(18, 7, 19),
        code(0, 8, 107),
        code(0, 8, 43),
        code(0, 9, 182),
        code(0, 8, 11),
        code(0, 8, 139),
        code(0, 8, 75),
        code(0, 9, 246),
    ]
);
fixed_literal_block!(
    fixed_literal_224,
    224,
    [
        code(16, 7, 5),
        code(0, 8, 87),
        code(0, 8, 23),
        code(64, 8, 0),
        code(19, 7, 51),
        code(0, 8, 119),
        code(0, 8, 55),
        code(0, 9, 206),
        code(17, 7, 15),
        code(0, 8, 103),
        code(0, 8, 39),
        code(0, 9, 174),
        code(0, 8, 7),
        code(0, 8, 135),
        code(0, 8, 71),
        code(0, 9, 238),
    ]
);
fixed_literal_block!(
    fixed_literal_240,
    240,
    [
        code(16, 7, 9),
        code(0, 8, 95),
        code(0, 8, 31),
        code(0, 9, 158),
        code(20, 7, 99),
        code(0, 8, 127),
        code(0, 8, 63),
        code(0, 9, 222),
        code(18, 7, 27),
        code(0, 8, 111),
        code(0, 8, 47),
        code(0, 9, 190),
        code(0, 8, 15),
        code(0, 8, 143),
        code(0, 8, 79),
        code(0, 9, 254),
    ]
);
fixed_literal_block!(
    fixed_literal_256,
    256,
    [
        code(96, 7, 0),
        code(0, 8, 80),
        code(0, 8, 16),
        code(20, 8, 115),
        code(18, 7, 31),
        code(0, 8, 112),
        code(0, 8, 48),
        code(0, 9, 193),
        code(16, 7, 10),
        code(0, 8, 96),
        code(0, 8, 32),
        code(0, 9, 161),
        code(0, 8, 0),
        code(0, 8, 128),
        code(0, 8, 64),
        code(0, 9, 225),
    ]
);
fixed_literal_block!(
    fixed_literal_272,
    272,
    [
        code(16, 7, 6),
        code(0, 8, 88),
        code(0, 8, 24),
        code(0, 9, 145),
        code(19, 7, 59),
        code(0, 8, 120),
        code(0, 8, 56),
        code(0, 9, 209),
        code(17, 7, 17),
        code(0, 8, 104),
        code(0, 8, 40),
        code(0, 9, 177),
        code(0, 8, 8),
        code(0, 8, 136),
        code(0, 8, 72),
        code(0, 9, 241),
    ]
);
fixed_literal_block!(
    fixed_literal_288,
    288,
    [
        code(16, 7, 4),
        code(0, 8, 84),
        code(0, 8, 20),
        code(21, 8, 227),
        code(19, 7, 43),
        code(0, 8, 116),
        code(0, 8, 52),
        code(0, 9, 201),
        code(17, 7, 13),
        code(0, 8, 100),
        code(0, 8, 36),
        code(0, 9, 169),
        code(0, 8, 4),
        code(0, 8, 132),
        code(0, 8, 68),
        code(0, 9, 233),
    ]
);
fixed_literal_block!(
    fixed_literal_304,
    304,
    [
        code(16, 7, 8),
        code(0, 8, 92),
        code(0, 8, 28),
        code(0, 9, 153),
        code(20, 7, 83),
        code(0, 8, 124),
        code(0, 8, 60),
        code(0, 9, 217),
        code(18, 7, 23),
        code(0, 8, 108),
        code(0, 8, 44),
        code(0, 9, 185),
        code(0, 8, 12),
        code(0, 8, 140),
        code(0, 8, 76),
        code(0, 9, 249),
    ]
);
fixed_literal_block!(
    fixed_literal_320,
    320,
    [
        code(16, 7, 3),
        code(0, 8, 82),
        code(0, 8, 18),
        code(21, 8, 163),
        code(19, 7, 35),
        code(0, 8, 114),
        code(0, 8, 50),
        code(0, 9, 197),
        code(17, 7, 11),
        code(0, 8, 98),
        code(0, 8, 34),
        code(0, 9, 165),
        code(0, 8, 2),
        code(0, 8, 130),
        code(0, 8, 66),
        code(0, 9, 229),
    ]
);
fixed_literal_block!(
    fixed_literal_336,
    336,
    [
        code(16, 7, 7),
        code(0, 8, 90),
        code(0, 8, 26),
        code(0, 9, 149),
        code(20, 7, 67),
        code(0, 8, 122),
        code(0, 8, 58),
        code(0, 9, 213),
        code(18, 7, 19),
        code(0, 8, 106),
        code(0, 8, 42),
        code(0, 9, 181),
        code(0, 8, 10),
        code(0, 8, 138),
        code(0, 8, 74),
        code(0, 9, 245),
    ]
);
fixed_literal_block!(
    fixed_literal_352,
    352,
    [
        code(16, 7, 5),
        code(0, 8, 86),
        code(0, 8, 22),
        code(64, 8, 0),
        code(19, 7, 51),
        code(0, 8, 118),
        code(0, 8, 54),
        code(0, 9, 205),
        code(17, 7, 15),
        code(0, 8, 102),
        code(0, 8, 38),
        code(0, 9, 173),
        code(0, 8, 6),
        code(0, 8, 134),
        code(0, 8, 70),
        code(0, 9, 237),
    ]
);
fixed_literal_block!(
    fixed_literal_368,
    368,
    [
        code(16, 7, 9),
        code(0, 8, 94),
        code(0, 8, 30),
        code(0, 9, 157),
        code(20, 7, 99),
        code(0, 8, 126),
        code(0, 8, 62),
        code(0, 9, 221),
        code(18, 7, 27),
        code(0, 8, 110),
        code(0, 8, 46),
        code(0, 9, 189),
        code(0, 8, 14),
        code(0, 8, 142),
        code(0, 8, 78),
        code(0, 9, 253),
    ]
);
fixed_literal_block!(
    fixed_literal_384,
    384,
    [
        code(96, 7, 0),
        code(0, 8, 81),
        code(0, 8, 17),
        code(21, 8, 131),
        code(18, 7, 31),
        code(0, 8, 113),
        code(0, 8, 49),
        code(0, 9, 195),
        code(16, 7, 10),
        code(0, 8, 97),
        code(0, 8, 33),
        code(0, 9, 163),
        code(0, 8, 1),
        code(0, 8, 129),
        code(0, 8, 65),
        code(0, 9, 227),
    ]
);
fixed_literal_block!(
    fixed_literal_400,
    400,
    [
        code(16, 7, 6),
        code(0, 8, 89),
        code(0, 8, 25),
        code(0, 9, 147),
        code(19, 7, 59),
        code(0, 8, 121),
        code(0, 8, 57),
        code(0, 9, 211),
        code(17, 7, 17),
        code(0, 8, 105),
        code(0, 8, 41),
        code(0, 9, 179),
        code(0, 8, 9),
        code(0, 8, 137),
        code(0, 8, 73),
        code(0, 9, 243),
    ]
);
fixed_literal_block!(
    fixed_literal_416,
    416,
    [
        code(16, 7, 4),
        code(0, 8, 85),
        code(0, 8, 21),
        code(16, 8, 258),
        code(19, 7, 43),
        code(0, 8, 117),
        code(0, 8, 53),
        code(0, 9, 203),
        code(17, 7, 13),
        code(0, 8, 101),
        code(0, 8, 37),
        code(0, 9, 171),
        code(0, 8, 5),
        code(0, 8, 133),
        code(0, 8, 69),
        code(0, 9, 235),
    ]
);
fixed_literal_block!(
    fixed_literal_432,
    432,
    [
        code(16, 7, 8),
        code(0, 8, 93),
        code(0, 8, 29),
        code(0, 9, 155),
        code(20, 7, 83),
        code(0, 8, 125),
        code(0, 8, 61),
        code(0, 9, 219),
        code(18, 7, 23),
        code(0, 8, 109),
        code(0, 8, 45),
        code(0, 9, 187),
        code(0, 8, 13),
        code(0, 8, 141),
        code(0, 8, 77),
        code(0, 9, 251),
    ]
);
fixed_literal_block!(
    fixed_literal_448,
    448,
    [
        code(16, 7, 3),
        code(0, 8, 83),
        code(0, 8, 19),
        code(21, 8, 195),
        code(19, 7, 35),
        code(0, 8, 115),
        code(0, 8, 51),
        code(0, 9, 199),
        code(17, 7, 11),
        code(0, 8, 99),
        code(0, 8, 35),
        code(0, 9, 167),
        code(0, 8, 3),
        code(0, 8, 131),
        code(0, 8, 67),
        code(0, 9, 231),
    ]
);
fixed_literal_block!(
    fixed_literal_464,
    464,
    [
        code(16, 7, 7),
        code(0, 8, 91),
        code(0, 8, 27),
        code(0, 9, 151),
        code(20, 7, 67),
        code(0, 8, 123),
        code(0, 8, 59),
        code(0, 9, 215),
        code(18, 7, 19),
        code(0, 8, 107),
        code(0, 8, 43),
        code(0, 9, 183),
        code(0, 8, 11),
        code(0, 8, 139),
        code(0, 8, 75),
        code(0, 9, 247),
    ]
);
fixed_literal_block!(
    fixed_literal_480,
    480,
    [
        code(16, 7, 5),
        code(0, 8, 87),
        code(0, 8, 23),
        code(64, 8, 0),
        code(19, 7, 51),
        code(0, 8, 119),
        code(0, 8, 55),
        code(0, 9, 207),
        code(17, 7, 15),
        code(0, 8, 103),
        code(0, 8, 39),
        code(0, 9, 175),
        code(0, 8, 7),
        code(0, 8, 135),
        code(0, 8, 71),
        code(0, 9, 239),
    ]
);
fixed_literal_block!(
    fixed_literal_496,
    496,
    [
        code(16, 7, 9),
        code(0, 8, 95),
        code(0, 8, 31),
        code(0, 9, 159),
        code(20, 7, 99),
        code(0, 8, 127),
        code(0, 8, 63),
        code(0, 9, 223),
        code(18, 7, 27),
        code(0, 8, 111),
        code(0, 8, 47),
        code(0, 9, 191),
        code(0, 8, 15),
        code(0, 8, 143),
        code(0, 8, 79),
        code(0, 9, 255),
    ]
);

#[cfg_attr(verus_keep_ghost, cfg_eval)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures forall|index: int| 0 <= index < 512 ==>
        #[trigger] result@[index] == crate::fixed_tree_specs::literal_entry(index),
))]
const fn build_fixed_literal_table() -> [Code; 512] {
    let rows = [
        fixed_literal_000(),
        fixed_literal_016(),
        fixed_literal_032(),
        fixed_literal_048(),
        fixed_literal_064(),
        fixed_literal_080(),
        fixed_literal_096(),
        fixed_literal_112(),
        fixed_literal_128(),
        fixed_literal_144(),
        fixed_literal_160(),
        fixed_literal_176(),
        fixed_literal_192(),
        fixed_literal_208(),
        fixed_literal_224(),
        fixed_literal_240(),
        fixed_literal_256(),
        fixed_literal_272(),
        fixed_literal_288(),
        fixed_literal_304(),
        fixed_literal_320(),
        fixed_literal_336(),
        fixed_literal_352(),
        fixed_literal_368(),
        fixed_literal_384(),
        fixed_literal_400(),
        fixed_literal_416(),
        fixed_literal_432(),
        fixed_literal_448(),
        fixed_literal_464(),
        fixed_literal_480(),
        fixed_literal_496(),
    ];
    let mut table = [code(0, 0, 0); 512];
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= 512,
            forall|row: int, column: int| 0 <= row < 32 && 0 <= column < 16 ==>
                #[trigger] rows@[row]@[column]
                    == crate::fixed_tree_specs::literal_entry(16 * row + column),
            forall|cell: int| 0 <= cell < index ==>
                #[trigger] table@[cell] == crate::fixed_tree_specs::literal_entry(cell),
        decreases 512 - index,
    ))]
    while index < 512 {
        table[index] = rows[index / 16][index % 16];
        index += 1;
    }
    table
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures forall|index: int| 0 <= index < 32 ==>
        #[trigger] DISTFIX@[index] == crate::fixed_tree_specs::distance_entry(index),
))]
pub(crate) const DISTFIX: [Code; 32] = build_fixed_distance_table();

#[cfg_attr(verus_keep_ghost, cfg_eval)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures forall|index: int| 0 <= index < 32 ==>
        #[trigger] result@[index] == crate::fixed_tree_specs::distance_entry(index),
))]
const fn build_fixed_distance_table() -> [Code; 32] {
    let table = [
        code(16, 5, 1),
        code(23, 5, 257),
        code(19, 5, 17),
        code(27, 5, 4097),
        code(17, 5, 5),
        code(25, 5, 1025),
        code(21, 5, 65),
        code(29, 5, 16385),
        code(16, 5, 3),
        code(24, 5, 513),
        code(20, 5, 33),
        code(28, 5, 8193),
        code(18, 5, 9),
        code(26, 5, 2049),
        code(22, 5, 129),
        code(64, 5, 0),
        code(16, 5, 2),
        code(23, 5, 385),
        code(19, 5, 25),
        code(27, 5, 6145),
        code(17, 5, 7),
        code(25, 5, 1537),
        code(21, 5, 97),
        code(29, 5, 24577),
        code(16, 5, 4),
        code(24, 5, 769),
        code(20, 5, 49),
        code(28, 5, 12289),
        code(18, 5, 13),
        code(26, 5, 3073),
        code(22, 5, 193),
        code(64, 5, 0),
    ];
    #[cfg(verus_keep_ghost)]
    proof! {
        let produced = table@;
        assert forall|index: int| 0 <= index < 32 implies
            #[trigger] produced[index] == crate::fixed_tree_specs::distance_entry(index) by {
            if index == 0 { assert(produced[0] == crate::fixed_tree_specs::distance_entry(0)) by (compute); }
            else if index == 1 { assert(produced[1] == crate::fixed_tree_specs::distance_entry(1)) by (compute); }
            else if index == 2 { assert(produced[2] == crate::fixed_tree_specs::distance_entry(2)) by (compute); }
            else if index == 3 { assert(produced[3] == crate::fixed_tree_specs::distance_entry(3)) by (compute); }
            else if index == 4 { assert(produced[4] == crate::fixed_tree_specs::distance_entry(4)) by (compute); }
            else if index == 5 { assert(produced[5] == crate::fixed_tree_specs::distance_entry(5)) by (compute); }
            else if index == 6 { assert(produced[6] == crate::fixed_tree_specs::distance_entry(6)) by (compute); }
            else if index == 7 { assert(produced[7] == crate::fixed_tree_specs::distance_entry(7)) by (compute); }
            else if index == 8 { assert(produced[8] == crate::fixed_tree_specs::distance_entry(8)) by (compute); }
            else if index == 9 { assert(produced[9] == crate::fixed_tree_specs::distance_entry(9)) by (compute); }
            else if index == 10 { assert(produced[10] == crate::fixed_tree_specs::distance_entry(10)) by (compute); }
            else if index == 11 { assert(produced[11] == crate::fixed_tree_specs::distance_entry(11)) by (compute); }
            else if index == 12 { assert(produced[12] == crate::fixed_tree_specs::distance_entry(12)) by (compute); }
            else if index == 13 { assert(produced[13] == crate::fixed_tree_specs::distance_entry(13)) by (compute); }
            else if index == 14 { assert(produced[14] == crate::fixed_tree_specs::distance_entry(14)) by (compute); }
            else if index == 15 { assert(produced[15] == crate::fixed_tree_specs::distance_entry(15)) by (compute); }
            else if index == 16 { assert(produced[16] == crate::fixed_tree_specs::distance_entry(16)) by (compute); }
            else if index == 17 { assert(produced[17] == crate::fixed_tree_specs::distance_entry(17)) by (compute); }
            else if index == 18 { assert(produced[18] == crate::fixed_tree_specs::distance_entry(18)) by (compute); }
            else if index == 19 { assert(produced[19] == crate::fixed_tree_specs::distance_entry(19)) by (compute); }
            else if index == 20 { assert(produced[20] == crate::fixed_tree_specs::distance_entry(20)) by (compute); }
            else if index == 21 { assert(produced[21] == crate::fixed_tree_specs::distance_entry(21)) by (compute); }
            else if index == 22 { assert(produced[22] == crate::fixed_tree_specs::distance_entry(22)) by (compute); }
            else if index == 23 { assert(produced[23] == crate::fixed_tree_specs::distance_entry(23)) by (compute); }
            else if index == 24 { assert(produced[24] == crate::fixed_tree_specs::distance_entry(24)) by (compute); }
            else if index == 25 { assert(produced[25] == crate::fixed_tree_specs::distance_entry(25)) by (compute); }
            else if index == 26 { assert(produced[26] == crate::fixed_tree_specs::distance_entry(26)) by (compute); }
            else if index == 27 { assert(produced[27] == crate::fixed_tree_specs::distance_entry(27)) by (compute); }
            else if index == 28 { assert(produced[28] == crate::fixed_tree_specs::distance_entry(28)) by (compute); }
            else if index == 29 { assert(produced[29] == crate::fixed_tree_specs::distance_entry(29)) by (compute); }
            else if index == 30 { assert(produced[30] == crate::fixed_tree_specs::distance_entry(30)) by (compute); }
            else { assert(index == 31); assert(produced[31] == crate::fixed_tree_specs::distance_entry(31)) by (compute); }
        }
    }
    table
}
