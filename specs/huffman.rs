use crate::huffman::InflateTable;
use crate::Code;
use vstd::prelude::*;

verus! {

pub enum Alphabet {
    CodeLengths,
    LiteralLengths,
    Distances,
}

pub open spec fn symbol_domain(alphabet: Alphabet, symbol: nat) -> bool {
    match alphabet {
        Alphabet::CodeLengths => symbol <= 18,
        Alphabet::LiteralLengths => symbol <= 287,
        Alphabet::Distances => symbol <= 31,
    }
}

pub open spec fn length_extra(symbol: nat) -> nat
    recommends 257 <= symbol <= 285,
{
    if symbol <= 264 || symbol == 285 { 0 }
    else { ((symbol - 261) / 4) as nat }
}

pub open spec fn length_base(symbol: nat) -> int
    recommends 257 <= symbol <= 285,
{
    if symbol <= 264 { symbol - 254 }
    else if symbol == 285 { 258 }
    else {
        3 + capacity(length_extra(symbol) + 2)
            + ((symbol - 265) % 4) * capacity(length_extra(symbol))
    }
}

pub open spec fn distance_extra(symbol: nat) -> nat
    recommends symbol <= 29,
{
    if symbol <= 3 { 0 } else { (symbol / 2 - 1) as nat }
}

pub open spec fn distance_base(symbol: nat) -> int
    recommends symbol <= 29,
{
    if symbol <= 3 { symbol as int + 1 }
    else {
        1 + capacity(distance_extra(symbol) + 1)
            + (symbol % 2) * capacity(distance_extra(symbol))
    }
}

pub open spec fn invalid_operation(op: u8) -> bool {
    op & 16 == 0 && op & 32 == 0 && op & 64 != 0
}

pub open spec fn entry_meaning(alphabet: Alphabet, symbol: nat, op: u8, value: u16) -> bool {
    match alphabet {
        Alphabet::CodeLengths => op == 0 && value == symbol,
        Alphabet::LiteralLengths => {
            if symbol < 256 { op == 0 && value == symbol }
            else if symbol == 256 { op == 96 && value == 0 }
            else if symbol <= 285 {
                op == 16 + length_extra(symbol) && value == length_base(symbol)
            } else { invalid_operation(op) && value == 0 }
        },
        Alphabet::Distances => {
            if symbol <= 29 {
                op == 16 + distance_extra(symbol) && value == distance_base(symbol)
            } else { invalid_operation(op) && value == 0 }
        },
    }
}

pub open spec fn tables_match(alphabet: Alphabet, base: Seq<u16>, extra: Seq<u8>,
    threshold: u16) -> bool {
    match alphabet {
        Alphabet::CodeLengths => base.len() == 0 && extra.len() == 0 && threshold == 20,
        Alphabet::LiteralLengths => base.len() == 31 && extra.len() == 31 && threshold == 257
            && (forall|index: int| 0 <= index < 29 ==>
                #[trigger] base[index] == length_base((index + 257) as nat)
                    && #[trigger] extra[index] == 16 + length_extra((index + 257) as nat))
            && (forall|index: int| 29 <= index < 31 ==>
                #[trigger] base[index] == 0 && invalid_operation(#[trigger] extra[index])),
        Alphabet::Distances => base.len() == 32 && extra.len() == 32 && threshold == 0
            && (forall|index: int| 0 <= index < 30 ==>
                #[trigger] base[index] == distance_base(index as nat)
                    && #[trigger] extra[index] == 16 + distance_extra(index as nat))
            && (forall|index: int| 30 <= index < 32 ==>
                #[trigger] base[index] == 0 && invalid_operation(#[trigger] extra[index])),
    }
}

pub open spec fn occurrences(lengths: Seq<u16>, value: u16) -> nat
    decreases lengths.len(),
{
    if lengths.len() == 0 { 0 }
    else {
        occurrences(lengths.drop_last(), value)
            + if lengths.last() == value { 1nat } else { 0nat }
    }
}

pub open spec fn minimum_length(lengths: Seq<u16>) -> usize
    decreases lengths.len(),
{
    if lengths.len() == 0 { 15 }
    else {
        let previous = minimum_length(lengths.drop_last());
        let current = lengths.last() as usize;
        if current > 0 && current < previous { current } else { previous }
    }
}

pub open spec fn maximum_length(lengths: Seq<u16>) -> usize
    decreases lengths.len(),
{
    if lengths.len() == 0 { 0 }
    else {
        let previous = maximum_length(lengths.drop_last());
        let current = lengths.last() as usize;
        if current > previous { current } else { previous }
    }
}

pub open spec fn histogram(lengths: Seq<u16>) -> Seq<u16> {
    Seq::new(16, |value: int|
        if value == 0 { 0u16 } else { occurrences(lengths, value as u16) as u16 })
}

pub open spec fn valid_histogram(lengths: Seq<u16>, counts: Seq<u16>) -> bool {
    counts.len() == 16 && counts[0] == 0
        && forall|value: int| 1 <= value <= 15 ==>
            counts[value] == occurrences(lengths, value as u16)
}

pub open spec fn before(counts: Seq<u16>, level: nat) -> nat
    recommends level <= counts.len(),
    decreases level,
{
    if level <= 1 { 0 }
    else { before(counts, (level - 1) as nat) + counts[level as int - 1] as nat }
}

pub open spec fn count_before(lengths: Seq<u16>, level: nat) -> nat
    decreases lengths.len(),
{
    if lengths.len() == 0 { 0 }
    else {
        count_before(lengths.drop_last(), level)
            + if 0 < lengths.last() && (lengths.last() as nat) < level { 1nat } else { 0nat }
    }
}

pub open spec fn bucket_entry(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    level: int, ordinal: int) -> bool
    recommends counts.len() == 16, 1 <= level <= 15,
{
    let position = before(counts, level as nat) as int + ordinal;
    0 <= position < work.len() && {
        let symbol = work[position] as int;
        symbol < lengths.len() && lengths[symbol] == level
            && occurrences(lengths.take(symbol), level as u16) == ordinal
    }
}

pub open spec fn bucket_ordered(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>) -> bool {
    counts.len() == 16
        && forall|level: int, ordinal: int|
            1 <= level <= 15 && 0 <= ordinal < counts[level] ==>
                #[trigger] bucket_entry(lengths, counts, work, level, ordinal)
}

pub open spec fn first_code(counts: Seq<u16>, depth: nat) -> nat
    recommends 1 <= depth <= counts.len(),
    decreases depth,
{
    if depth <= 1 { 0 }
    else { 2 * (first_code(counts, (depth - 1) as nat) + counts[depth as int - 1] as nat) }
}

pub open spec fn canonical_start(lengths: Seq<u16>, depth: nat) -> nat
    recommends 1 <= depth <= 15,
    decreases depth,
{
    if depth <= 1 { 0 }
    else {
        2 * (canonical_start(lengths, (depth - 1) as nat)
            + occurrences(lengths, (depth - 1) as u16))
    }
}

pub open spec fn canonical_code(lengths: Seq<u16>, symbol: int) -> nat
    recommends 0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
{
    canonical_start(lengths, lengths[symbol] as nat)
        + occurrences(lengths.take(symbol), lengths[symbol])
}

pub open spec fn canonical_interval_contains(lengths: Seq<u16>, symbol: int, index: int) -> bool {
    0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15
        && canonical_code(lengths, symbol) * capacity((32 - lengths[symbol]) as nat) <= index
        < (canonical_code(lengths, symbol) + 1) * capacity((32 - lengths[symbol]) as nat)
}

pub open spec fn normalized_cursor(counts: Seq<u16>, level: nat, position: nat) -> int
    recommends counts.len() == 16, 1 <= level <= 15,
{
    (first_code(counts, level) + position - before(counts, level))
        * capacity((32 - level) as nat)
}

pub open spec fn word_bit(word: u32, index: u32) -> u32
    recommends index < 32,
{
    (word >> index) & 1
}

pub open spec fn aligned_cursor(word: u32, length: u32) -> bool
    recommends 1 <= length <= 15,
{
    word & (u32::MAX >> length) == 0
}

pub open spec fn is_reversal(word: u32, reversed: u32) -> bool {
    forall|index: u32| index < 32 ==> #[trigger] word_bit(reversed, index)
        == word_bit(word, (31 - index) as u32)
}

pub open spec fn reversed_word(word: u32) -> u32 {
    choose|reversed: u32| is_reversal(word, reversed)
}

pub open spec fn canonical_prefix(lengths: Seq<u16>, symbol: int) -> u32
    recommends 0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
{
    reversed_word((canonical_code(lengths, symbol)
        * capacity((32 - lengths[symbol]) as nat)) as u32)
}

pub open spec fn code_prefix_matches(lengths: Seq<u16>, symbol: int, word: u32) -> bool {
    0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15
        && (word as int) % capacity(lengths[symbol] as nat)
            == canonical_prefix(lengths, symbol)
}

pub open spec fn code_length_source_prefix(lengths: Seq<u16>, symbol: int,
    source: Seq<bool>) -> bool {
    0 <= symbol < lengths.len() && symbol <= 18 && 1 <= lengths[symbol] <= 7
        && lengths[symbol] <= source.len()
        && crate::bit_specs::low_first_value(source.take(lengths[symbol] as int))
            == canonical_prefix(lengths, symbol)
}

pub(crate) open spec fn root_entry_decodes(lengths: Seq<u16>, entry: Code, word: u32) -> bool {
    exists|symbol: int| #[trigger] code_prefix_matches(lengths, symbol, word)
        && symbol_domain(Alphabet::CodeLengths, symbol as nat)
        && entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 }
        && (forall|other: int| #[trigger] code_prefix_matches(lengths, other, word)
            ==> other == symbol)
}

pub(crate) open spec fn root_decoding_table(lengths: Seq<u16>, table: Seq<Code>) -> bool {
    1 <= maximum_length(lengths) <= 7
        && capacity(maximum_length(lengths) as nat) <= table.len()
        && forall|index: int| 0 <= index < capacity(maximum_length(lengths) as nat) ==>
            #[trigger] root_entry_decodes(lengths, table[index], index as u32)
}

#[verifier::opaque]
pub(crate) open spec fn header_decoding_table(lengths: Seq<u16>, table: Seq<Code>,
    root: usize) -> bool {
    lengths.len() == 19
        && if maximum_length(lengths) == 0 {
            root == 1 && table.len() >= 2
                && table[0] == Code { op: 64, bits: 1, val: 0 }
                && table[1] == Code { op: 64, bits: 1, val: 0 }
        } else {
            root == maximum_length(lengths) && root_decoding_table(lengths, table)
        }
}

pub(crate) open spec fn code_length_result(lengths: Seq<u16>, before_table: Seq<Code>,
    table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>, result: InflateTable) -> bool {
    table.len() == before_table.len() && work.len() == before_work.len()
        && match result {
            InflateTable::EnoughIsNotEnough => false,
            InflateTable::InvalidCode => maximum_length(lengths) > 0
                && !accepted_lengths(lengths, true)
                && table == before_table && work == before_work,
            InflateTable::Success { root, used } => {
                if maximum_length(lengths) == 0 {
                    root == 1 && used == 2 && work == before_work
                        && forall|index: int| 0 <= index < before_table.len() ==>
                            #[trigger] table[index] == if index < 2 {
                                Code { op: 64, bits: 1, val: 0 }
                            } else { before_table[index] }
                } else {
                    accepted_lengths(lengths, true)
                        && root == maximum_length(lengths) && used == capacity(root as nat)
                        && root_codes_table(lengths, work, before(histogram(lengths), 16),
                            table, before_table)
                        && root_decoding_table(lengths, table)
                        && (forall|index: int| used <= index < before_table.len() ==>
                            #[trigger] table[index] == before_table[index])
                        && (forall|index: int| before(histogram(lengths), 16) <= index
                            < before_work.len() ==> #[trigger] work[index] == before_work[index])
                }
            },
        }
}

#[verifier::opaque]
pub(crate) open spec fn root_codes_after(lengths: Seq<u16>, work: Seq<u16>,
    processed: nat, index: int, original: Code) -> Code
    decreases processed,
{
    if processed == 0 { original }
    else {
        let position = processed as int - 1;
        let symbol = work[position];
        let length = lengths[symbol as int];
        if table_replica(0, canonical_prefix(lengths, symbol as int) as nat,
            length as nat, maximum_length(lengths) as nat, index) {
            Code { op: 0, bits: length as u8, val: symbol }
        } else {
            root_codes_after(lengths, work, (processed - 1) as nat, index, original)
        }
    }
}

pub(crate) open spec fn root_codes_table(lengths: Seq<u16>, work: Seq<u16>,
    processed: nat, table: Seq<Code>, original: Seq<Code>) -> bool {
    bucket_ordered(lengths, histogram(lengths), work)
        && processed <= before(histogram(lengths), 16)
        && table.len() == original.len()
        && forall|index: int| 0 <= index < table.len() ==>
            #[trigger] table[index]
                == root_codes_after(lengths, work, processed, index, original[index])
}

pub open spec fn table_replica(base: nat, prefix: nat, code_bits: nat, table_bits: nat,
    index: int) -> bool {
    base <= index < base + capacity(table_bits)
        && (index - base) % capacity(code_bits) == prefix
}

pub(crate) open spec fn subtable_link(entry: Code, root: nat, next: nat, width: nat,
    used: nat) -> bool {
    1 <= root && 1 <= width && root + width <= 15
        && capacity(root) <= next
        && used == next + capacity(width)
        && entry.bits == root && entry.op == width && entry.val == next
}

pub(crate) open spec fn subtable_index(entry: Code, word: nat) -> int
    recommends 1 <= entry.bits <= 15, 1 <= entry.op <= 15,
{
    entry.val as int + ((word as int) / capacity(entry.bits as nat)) % capacity(entry.op as nat)
}

pub(crate) open spec fn subtable_link_result(before: Seq<Code>, after: Seq<Code>,
    prefix: nat, root: nat, previous_used: nat, next: nat, width: nat,
    used: nat, accepted: bool) -> bool {
    next == previous_used && after.len() == before.len()
        && if accepted {
            prefix < capacity(root) <= after.len()
                && subtable_link(after[prefix as int], root, next, width, used)
                && forall|index: int| 0 <= index < after.len() && index != prefix ==>
                    #[trigger] after[index] == before[index]
        } else { after == before }
}

pub open spec fn lookahead_space(counts: Seq<u16>, start: nat, drop: nat, depth: nat) -> int
    recommends counts.len() == 16, 1 <= start <= depth, depth + drop <= 15,
    decreases depth,
{
    if depth <= start { capacity(start) }
    else {
        2 * (lookahead_space(counts, start, drop, (depth - 1) as nat)
            - counts[(depth + drop - 1) as int] as int)
    }
}

pub open spec fn chosen_width(counts: Seq<u16>, start: nat, drop: nat, max: nat,
    width: nat) -> bool {
    start <= width && width + drop <= max
        && lookahead_space(counts, start, drop, width) > 0
        && (forall|depth: nat| start <= depth < width ==>
            #[trigger] lookahead_space(counts, start, drop, depth)
                - counts[(depth + drop) as int] > 0)
        && (width + drop < max ==>
            lookahead_space(counts, start, drop, width) - counts[(width + drop) as int] <= 0)
}

pub open spec fn remaining_count(counts: Seq<u16>, level: nat, processed: nat) -> nat
    recommends counts.len() == 16, 1 <= level <= 15,
{
    let start = before(counts, level);
    let end = start + counts[level as int] as nat;
    if processed <= start { counts[level as int] as nat }
    else if end <= processed { 0 }
    else { (end - processed) as nat }
}

pub open spec fn remaining_histogram(counts: Seq<u16>, current: Seq<u16>, processed: nat) -> bool {
    counts.len() == 16 && current.len() == 16 && current[0] == 0
        && forall|level: int| 1 <= level <= 15 ==>
            current[level] == remaining_count(counts, level as nat, processed)
}

pub open spec fn accepted_lengths(lengths: Seq<u16>, require_complete: bool) -> bool {
    maximum_length(lengths) > 0
        && valid_prefix(histogram(lengths), 15)
        && (slots(histogram(lengths), 15) == 0
            || (!require_complete && maximum_length(lengths) == 1))
}

// Each tree level doubles the available prefixes before assigning symbols.
pub open spec fn slots(counts: Seq<u16>, depth: nat) -> int
    recommends depth < counts.len(),
    decreases depth,
{
    if depth == 0 { 1 }
    else { 2 * slots(counts, (depth - 1) as nat) - counts[depth as int] }
}

pub open spec fn valid_prefix(counts: Seq<u16>, depth: nat) -> bool {
    forall|level: nat| level <= depth ==> slots(counts, level) >= 0
}

pub open spec fn capacity(depth: nat) -> int
    decreases depth,
{
    if depth == 0 { 1 } else { 2 * capacity((depth - 1) as nat) }
}

}
