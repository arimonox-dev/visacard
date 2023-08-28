function compute() {
    this.P1600_ROUND_CONSTANTS = [1, 0, 32898, 0, 32906, 2147483648, 2147516416, 2147483648, 32907, 0, 2147483649, 0, 2147516545, 2147483648, 32777, 2147483648, 138, 0, 136, 0, 2147516425, 0, 2147483658, 0, 2147516555, 0, 139, 2147483648, 32905, 2147483648, 32771, 2147483648, 32770, 2147483648, 128, 2147483648, 32778, 0, 2147483658, 2147483648, 2147516545, 2147483648, 32896, 2147483648, 2147483649, 0, 2147516424, 2147483648]
    this.state = [
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0
    ]
    this.blockSize = null
    this.squeezing = false
    this.count = 0
    this.size = 256 / 8
}
compute.prototype.int = function (a, b = 256, c = 0n) {
    while (a.length) {
        a[0] = typeof a[0] == 'number' ? BigInt(a[0]) : a[0];
        c = c * BigInt(b) + a[0];
        a = a.slice(1);
    };
    return c
}
compute.prototype.uint = function (c, b = 256, a = []) {
    c = typeof c == 'number' ? BigInt(c) : c;
    while (c) {
        a.unshift(c % BigInt(b));
        c /= BigInt(b);
    }
    return a;
}
compute.prototype.At = function (char) {
    return char.split('').map(i => i.charCodeAt(0));
}

compute.prototype.hex = function (hex) {
    return '0x' + hex.match(/.{1,2}/g).map(i => i.padStart(2, 0)).join('');
}
compute.prototype.encode = function (value) {
    switch (typeof value) {
        case 'string':
            value = value.replace(/0x/, '');
            try {
                value = BigInt(this.hex(value)) == 0 ? this.int(this.At(value)) : BigInt(this.hex(value));
                value = this.uint(value).map(Number);
            } catch (e) {
                value = this.At(value);
            }
            break;
        case 'number':
            value = this.uint(BigInt(value)).map(Number);
            break;
        case 'bigint':
            value = this.uint(value).map(Number);
            break;
        default:
    }
    return value
}
compute.prototype.sha256 = function (ascii) {
    ascii = this.encode(ascii)
    function rightRotate(value, amount) {
        return (value >>> amount) | (value << (32 - amount));
    }
    var mathPow = Math.pow;
    var maxWord = mathPow(2, 32);
    var lengthProperty = 'length';
    var i, j;
    var result = '';
    var words = [];
    var asciiBitLength = ascii[lengthProperty] * 8;
    var hash = (this.sha256.h = this.sha256.h || []);
    var k = (this.sha256.k = this.sha256.k || []);
    var primeCounter = k[lengthProperty];
    var isComposite = {};
    for (var candidate = 2; primeCounter < 64; candidate++) {
        if (!isComposite[candidate]) {
            for (i = 0; i < 313; i += candidate) {
                isComposite[i] = candidate;
            }
            hash[primeCounter] = (mathPow(candidate, 0.5) * maxWord) | 0;
            k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
        }
    }
    ascii = ascii.concat(128)
    while ((ascii[lengthProperty] % 64) - 56) ascii = ascii.concat(0);
    for (i = 0; i < ascii[lengthProperty]; i++) {
        j = ascii[i];
        if (j >> 8) return;
        words[i >> 2] |= j << (((3 - i) % 4) * 8);
    }
    words[words[lengthProperty]] = (asciiBitLength / maxWord) | 0;
    words[words[lengthProperty]] = asciiBitLength;

    for (j = 0; j < words[lengthProperty];) {
        var w = words.slice(j, (j += 16));
        var oldHash = hash;
        hash = hash.slice(0, 8);

        for (i = 0; i < 64; i++) {
            var i2 = i + j;
            var w15 = w[i - 15],
                w2 = w[i - 2];
            var a = hash[0],
                e = hash[4];
            var temp1 =
                hash[7] +
                (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25)) + // S1
                ((e & hash[5]) ^ (~e & hash[6])) + // ch
                k[i] +
                (w[i] =
                    i < 16
                        ? w[i]
                        : (w[i - 16] +
                            (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15 >>> 3)) + // s0
                            w[i - 7] +
                            (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2 >>> 10))) | // s1
                        0);
            var temp2 =
                (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22)) +
                ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));

            hash = [(temp1 + temp2) | 0].concat(hash);
            hash[4] = (hash[4] + temp1) | 0;
        }

        for (i = 0; i < 8; i++) {
            hash[i] = (hash[i] + oldHash[i]) | 0;
        }
    }

    for (i = 0; i < 8; i++) {
        for (j = 3; j + 1; j--) {
            var b = (hash[i] >> (j * 8)) & 255;
            result += (b < 16 ? 0 : '') + b.toString(16);
        }
    }
    return result;
}

compute.prototype.hmac = function (k, d=0) {
    if (!k) { k = this.sha256('') }
    [k, d] = [k, d].map(i => this.encode(i))
    k = k.length > 64 ? this.encode(this.sha256(k)) : k.concat(Array(64 - k.length).fill(0));
    let ik = Array(64).fill(0);
    let ok = Array(64).fill(0);
    let size = 64;
    let i = 0;
    while (i < size) {
        ik[i] = 0x36 ^ k[i];
        ok[i] = 0x5c ^ k[i];
        i++;
    }
    let upd = new Uint8Array(d.length + 64);
    upd.set(ik, 0);
    upd.set(d, 64);
    upd = new Uint8Array(this.encode(this.sha256(Array.from(upd))))
    let res = new Uint8Array(64 + 32);
    res.set(ok, 0);
    res.set(upd, 64);
    res = Array.from(res);
    return this.sha256(res)
}
compute.prototype.block = function (s) {
    for (let round = 0; round < 24; ++round) {
        const lo0 = s[0] ^ s[10] ^ s[20] ^ s[30] ^ s[40]
        const hi0 = s[1] ^ s[11] ^ s[21] ^ s[31] ^ s[41]
        const lo1 = s[2] ^ s[12] ^ s[22] ^ s[32] ^ s[42]
        const hi1 = s[3] ^ s[13] ^ s[23] ^ s[33] ^ s[43]
        const lo2 = s[4] ^ s[14] ^ s[24] ^ s[34] ^ s[44]
        const hi2 = s[5] ^ s[15] ^ s[25] ^ s[35] ^ s[45]
        const lo3 = s[6] ^ s[16] ^ s[26] ^ s[36] ^ s[46]
        const hi3 = s[7] ^ s[17] ^ s[27] ^ s[37] ^ s[47]
        const lo4 = s[8] ^ s[18] ^ s[28] ^ s[38] ^ s[48]
        const hi4 = s[9] ^ s[19] ^ s[29] ^ s[39] ^ s[49]

        let lo = lo4 ^ (lo1 << 1 | hi1 >>> 31)
        let hi = hi4 ^ (hi1 << 1 | lo1 >>> 31)
        const t1slo0 = s[0] ^ lo
        const t1shi0 = s[1] ^ hi
        const t1slo5 = s[10] ^ lo
        const t1shi5 = s[11] ^ hi
        const t1slo10 = s[20] ^ lo
        const t1shi10 = s[21] ^ hi
        const t1slo15 = s[30] ^ lo
        const t1shi15 = s[31] ^ hi
        const t1slo20 = s[40] ^ lo
        const t1shi20 = s[41] ^ hi
        lo = lo0 ^ (lo2 << 1 | hi2 >>> 31)
        hi = hi0 ^ (hi2 << 1 | lo2 >>> 31)
        const t1slo1 = s[2] ^ lo
        const t1shi1 = s[3] ^ hi
        const t1slo6 = s[12] ^ lo
        const t1shi6 = s[13] ^ hi
        const t1slo11 = s[22] ^ lo
        const t1shi11 = s[23] ^ hi
        const t1slo16 = s[32] ^ lo
        const t1shi16 = s[33] ^ hi
        const t1slo21 = s[42] ^ lo
        const t1shi21 = s[43] ^ hi
        lo = lo1 ^ (lo3 << 1 | hi3 >>> 31)
        hi = hi1 ^ (hi3 << 1 | lo3 >>> 31)
        const t1slo2 = s[4] ^ lo
        const t1shi2 = s[5] ^ hi
        const t1slo7 = s[14] ^ lo
        const t1shi7 = s[15] ^ hi
        const t1slo12 = s[24] ^ lo
        const t1shi12 = s[25] ^ hi
        const t1slo17 = s[34] ^ lo
        const t1shi17 = s[35] ^ hi
        const t1slo22 = s[44] ^ lo
        const t1shi22 = s[45] ^ hi
        lo = lo2 ^ (lo4 << 1 | hi4 >>> 31)
        hi = hi2 ^ (hi4 << 1 | lo4 >>> 31)
        const t1slo3 = s[6] ^ lo
        const t1shi3 = s[7] ^ hi
        const t1slo8 = s[16] ^ lo
        const t1shi8 = s[17] ^ hi
        const t1slo13 = s[26] ^ lo
        const t1shi13 = s[27] ^ hi
        const t1slo18 = s[36] ^ lo
        const t1shi18 = s[37] ^ hi
        const t1slo23 = s[46] ^ lo
        const t1shi23 = s[47] ^ hi
        lo = lo3 ^ (lo0 << 1 | hi0 >>> 31)
        hi = hi3 ^ (hi0 << 1 | lo0 >>> 31)
        const t1slo4 = s[8] ^ lo
        const t1shi4 = s[9] ^ hi
        const t1slo9 = s[18] ^ lo
        const t1shi9 = s[19] ^ hi
        const t1slo14 = s[28] ^ lo
        const t1shi14 = s[29] ^ hi
        const t1slo19 = s[38] ^ lo
        const t1shi19 = s[39] ^ hi
        const t1slo24 = s[48] ^ lo
        const t1shi24 = s[49] ^ hi

        const t2slo0 = t1slo0
        const t2shi0 = t1shi0
        const t2slo16 = (t1shi5 << 4 | t1slo5 >>> 28)
        const t2shi16 = (t1slo5 << 4 | t1shi5 >>> 28)
        const t2slo7 = (t1slo10 << 3 | t1shi10 >>> 29)
        const t2shi7 = (t1shi10 << 3 | t1slo10 >>> 29)
        const t2slo23 = (t1shi15 << 9 | t1slo15 >>> 23)
        const t2shi23 = (t1slo15 << 9 | t1shi15 >>> 23)
        const t2slo14 = (t1slo20 << 18 | t1shi20 >>> 14)
        const t2shi14 = (t1shi20 << 18 | t1slo20 >>> 14)
        const t2slo10 = (t1slo1 << 1 | t1shi1 >>> 31)
        const t2shi10 = (t1shi1 << 1 | t1slo1 >>> 31)
        const t2slo1 = (t1shi6 << 12 | t1slo6 >>> 20)
        const t2shi1 = (t1slo6 << 12 | t1shi6 >>> 20)
        const t2slo17 = (t1slo11 << 10 | t1shi11 >>> 22)
        const t2shi17 = (t1shi11 << 10 | t1slo11 >>> 22)
        const t2slo8 = (t1shi16 << 13 | t1slo16 >>> 19)
        const t2shi8 = (t1slo16 << 13 | t1shi16 >>> 19)
        const t2slo24 = (t1slo21 << 2 | t1shi21 >>> 30)
        const t2shi24 = (t1shi21 << 2 | t1slo21 >>> 30)
        const t2slo20 = (t1shi2 << 30 | t1slo2 >>> 2)
        const t2shi20 = (t1slo2 << 30 | t1shi2 >>> 2)
        const t2slo11 = (t1slo7 << 6 | t1shi7 >>> 26)
        const t2shi11 = (t1shi7 << 6 | t1slo7 >>> 26)
        const t2slo2 = (t1shi12 << 11 | t1slo12 >>> 21)
        const t2shi2 = (t1slo12 << 11 | t1shi12 >>> 21)
        const t2slo18 = (t1slo17 << 15 | t1shi17 >>> 17)
        const t2shi18 = (t1shi17 << 15 | t1slo17 >>> 17)
        const t2slo9 = (t1shi22 << 29 | t1slo22 >>> 3)
        const t2shi9 = (t1slo22 << 29 | t1shi22 >>> 3)
        const t2slo5 = (t1slo3 << 28 | t1shi3 >>> 4)
        const t2shi5 = (t1shi3 << 28 | t1slo3 >>> 4)
        const t2slo21 = (t1shi8 << 23 | t1slo8 >>> 9)
        const t2shi21 = (t1slo8 << 23 | t1shi8 >>> 9)
        const t2slo12 = (t1slo13 << 25 | t1shi13 >>> 7)
        const t2shi12 = (t1shi13 << 25 | t1slo13 >>> 7)
        const t2slo3 = (t1slo18 << 21 | t1shi18 >>> 11)
        const t2shi3 = (t1shi18 << 21 | t1slo18 >>> 11)
        const t2slo19 = (t1shi23 << 24 | t1slo23 >>> 8)
        const t2shi19 = (t1slo23 << 24 | t1shi23 >>> 8)
        const t2slo15 = (t1slo4 << 27 | t1shi4 >>> 5)
        const t2shi15 = (t1shi4 << 27 | t1slo4 >>> 5)
        const t2slo6 = (t1slo9 << 20 | t1shi9 >>> 12)
        const t2shi6 = (t1shi9 << 20 | t1slo9 >>> 12)
        const t2slo22 = (t1shi14 << 7 | t1slo14 >>> 25)
        const t2shi22 = (t1slo14 << 7 | t1shi14 >>> 25)
        const t2slo13 = (t1slo19 << 8 | t1shi19 >>> 24)
        const t2shi13 = (t1shi19 << 8 | t1slo19 >>> 24)
        const t2slo4 = (t1slo24 << 14 | t1shi24 >>> 18)
        const t2shi4 = (t1shi24 << 14 | t1slo24 >>> 18)

        s[0] = t2slo0 ^ (~t2slo1 & t2slo2)
        s[1] = t2shi0 ^ (~t2shi1 & t2shi2)
        s[10] = t2slo5 ^ (~t2slo6 & t2slo7)
        s[11] = t2shi5 ^ (~t2shi6 & t2shi7)
        s[20] = t2slo10 ^ (~t2slo11 & t2slo12)
        s[21] = t2shi10 ^ (~t2shi11 & t2shi12)
        s[30] = t2slo15 ^ (~t2slo16 & t2slo17)
        s[31] = t2shi15 ^ (~t2shi16 & t2shi17)
        s[40] = t2slo20 ^ (~t2slo21 & t2slo22)
        s[41] = t2shi20 ^ (~t2shi21 & t2shi22)
        s[2] = t2slo1 ^ (~t2slo2 & t2slo3)
        s[3] = t2shi1 ^ (~t2shi2 & t2shi3)
        s[12] = t2slo6 ^ (~t2slo7 & t2slo8)
        s[13] = t2shi6 ^ (~t2shi7 & t2shi8)
        s[22] = t2slo11 ^ (~t2slo12 & t2slo13)
        s[23] = t2shi11 ^ (~t2shi12 & t2shi13)
        s[32] = t2slo16 ^ (~t2slo17 & t2slo18)
        s[33] = t2shi16 ^ (~t2shi17 & t2shi18)
        s[42] = t2slo21 ^ (~t2slo22 & t2slo23)
        s[43] = t2shi21 ^ (~t2shi22 & t2shi23)
        s[4] = t2slo2 ^ (~t2slo3 & t2slo4)
        s[5] = t2shi2 ^ (~t2shi3 & t2shi4)
        s[14] = t2slo7 ^ (~t2slo8 & t2slo9)
        s[15] = t2shi7 ^ (~t2shi8 & t2shi9)
        s[24] = t2slo12 ^ (~t2slo13 & t2slo14)
        s[25] = t2shi12 ^ (~t2shi13 & t2shi14)
        s[34] = t2slo17 ^ (~t2slo18 & t2slo19)
        s[35] = t2shi17 ^ (~t2shi18 & t2shi19)
        s[44] = t2slo22 ^ (~t2slo23 & t2slo24)
        s[45] = t2shi22 ^ (~t2shi23 & t2shi24)
        s[6] = t2slo3 ^ (~t2slo4 & t2slo0)
        s[7] = t2shi3 ^ (~t2shi4 & t2shi0)
        s[16] = t2slo8 ^ (~t2slo9 & t2slo5)
        s[17] = t2shi8 ^ (~t2shi9 & t2shi5)
        s[26] = t2slo13 ^ (~t2slo14 & t2slo10)
        s[27] = t2shi13 ^ (~t2shi14 & t2shi10)
        s[36] = t2slo18 ^ (~t2slo19 & t2slo15)
        s[37] = t2shi18 ^ (~t2shi19 & t2shi15)
        s[46] = t2slo23 ^ (~t2slo24 & t2slo20)
        s[47] = t2shi23 ^ (~t2shi24 & t2shi20)
        s[8] = t2slo4 ^ (~t2slo0 & t2slo1)
        s[9] = t2shi4 ^ (~t2shi0 & t2shi1)
        s[18] = t2slo9 ^ (~t2slo5 & t2slo6)
        s[19] = t2shi9 ^ (~t2shi5 & t2shi6)
        s[28] = t2slo14 ^ (~t2slo10 & t2slo11)
        s[29] = t2shi14 ^ (~t2shi10 & t2shi11)
        s[38] = t2slo19 ^ (~t2slo15 & t2slo16)
        s[39] = t2shi19 ^ (~t2shi15 & t2shi16)
        s[48] = t2slo24 ^ (~t2slo20 & t2slo21)
        s[49] = t2shi24 ^ (~t2shi20 & t2shi21)

        s[0] ^= this.P1600_ROUND_CONSTANTS[round * 2]
        s[1] ^= this.P1600_ROUND_CONSTANTS[round * 2 + 1]
    }
}
compute.prototype.keccak = function (rate = 1088, max = 256, capacity) {
    this.size = max / 8;
    this.initialize(rate, capacity);
    let enc = d => {
        this.absorb(this.At(d));
        return this.int(Array.from(this.squeeze(this.size))).toString(16).padStart(64,0);
    }
    return {
        update: function (mz) {
            return enc(mz);
        }
    }
}
compute.prototype.initialize = function (rate, capacity) {
    for (let i = 0; i < 50; ++i) this.state[i] = 0
    this.blockSize = rate / 8
    this.count = 0
    this.squeezing = false
}
compute.prototype.absorb = function (data) {
    for (let i = 0; i < data.length; ++i) {
        this.state[~~(this.count / 4)] ^= data[i] << (8 * (this.count % 4))
        this.count += 1
        if (this.count === this.blockSize) {
            this.block(this.state)
            this.count = 0
        }
    }
}
compute.prototype.absorbLastFewBits = function (bits) {
    this.state[~~(this.count / 4)] ^= bits << (8 * (this.count % 4))
    if ((bits & 0x80) !== 0 && this.count === (this.blockSize - 1)) this.block(this.state)
    this.state[~~((this.blockSize - 1) / 4)] ^= 0x80 << (8 * ((this.blockSize - 1) % 4))
    this.block(this.state)
    this.count = 0
    this.squeezing = true
}
compute.prototype.squeeze = function (length) {
    if (!this.squeezing) this.absorbLastFewBits(0x01)
    const output = new Uint8Array(length)
    for (let i = 0; i < length; ++i) {
        output[i] = (this.state[~~(this.count / 4)] >>> (8 * (this.count % 4))) & 0xff
        this.count += 1
        if (this.count === this.blockSize) {
            this.block(this.state)
            this.count = 0
        }
    }
    return output
}
compute.prototype.copy = function (dest) {
    for (let i = 0; i < 50; ++i) dest.state[i] = this.state[i]
    dest.blockSize = this.blockSize
    dest.count = this.count
    dest.squeezing = this.squeezing
}


let cm = new compute()
let tx = cm.keccak()
tx.final={}
console.log(cm, tx)