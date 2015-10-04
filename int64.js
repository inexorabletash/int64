(function(global) {

  var imul = Math.imul, abs = Math.abs, floor = Math.floor, pow = Math.pow;;

  var POW2_63 = pow(2, 63);
  var POW2_64 = pow(2, 64);
  var POW2_32 = pow(2, 32);

  function icmp(a, b) {
    var a0 = a.lo >>> 0, a1 = a.hi | 0;
    var b0 = b.lo >>> 0, b1 = b.hi | 0;
    if (a1 < b1) return -1;
    if (a1 > b1) return 1;
    if (a0 < b0) return -1;
    if (a0 > b0) return 1;
    return 0;
  }

  function ucmp(a, b) {
    var a0 = a.lo >>> 0, a1 = a.hi >>> 0;
    var b0 = b.lo >>> 0, b1 = b.hi >>> 0;
    if (a1 < b1) return -1;
    if (a1 > b1) return 1;
    if (a0 < b0) return -1;
    if (a0 > b0) return 1;
    return 0;
  }

  function eq(a, b) {
    return a.lo === b.lo && a.hi === b.hi;
  }

  function clz64(a) {
    return a.hi ? Math.clz32(a.hi) : Math.clz32(a.lo) + 32;
  }

  function lt0(a) { return (a.hi|0) < 0; }

  function negate(n) {
    var lo = n.lo >>> 0;
    var hi = n.hi >>> 0;
    var c0 = (-lo) >>> 0;
    var r = (lo | (~lo & c0)) >>> 31;
    var c1 = (-hi - r)|0;
    return {lo:c0, hi:c1};
  };

  function uadd(a, b) {
    var a0 = a.lo >>> 0, a1 = a.hi >>> 0;
    var b0 = b.lo >>> 0, b1 = b.hi >>> 0;

    var c0 = (a0 + b0) >>> 0;
    var c = ((a0 & b0) | (a0 | b0) & ~c0) >>> 31;
    var c1 = (a1 + b1 + c) >>> 0;
    return {lo: c0, hi: c1};
  }

  function usub(a, b) {
    var a0 = a.lo >>> 0, a1 = a.hi >>> 0;
    var b0 = b.lo >>> 0, b1 = b.hi >>> 0;

    var c0 = (a0 - b0) >>> 0;
    var r = ((~a0 & b0) | (~(a0 ^ b0) & c0)) >>> 31;
    var c1 = (a1 - b1 - r)|0;
    return {lo: c0, hi: c1};
  }

  function shl(a) {
    return {lo: a.lo << 1, hi: a.hi << 1 | a.lo >>> 31};
  }

  function shr(a) {
    return {lo: a.lo >> 1 | a.hi << 31, hi: a.hi >> 1};
  }

  function uor(a, b) {
    return {lo: a.lo | b.lo, hi: a.hi | b.hi};
  }

  function umul(a, b) {
    var c = uZERO;
    if (ucmp(a, b) < 0) { var tmp = a; a = b; b = tmp; }

    while (!eq(b, uZERO)) {
      if (b.lo & 1) c = uadd(c, a);
      b = shr(b);
      a = shl(a);
    }
    return c;
  }

  function udivrem(a, b) {
    switch(ucmp(a, b)) {
      case -1: return {quotient: uZERO, remainder: a};
      case 0:  return {quotient: uONE, remainder: uZERO};
    }

    var shift = clz64(b) - clz64(a);
    var divisor = Uint64.shiftLeft(b, shift);
    var remainder = a, quotient = uZERO;
    while (shift-- >= 0) {
      quotient = shl(quotient);
      if (icmp(remainder, divisor) >= 0) {
        remainder = usub(remainder, divisor);
        quotient = uor(quotient, uONE);
      }
      divisor = shr(divisor, 1);
    }

    return {quotient: quotient, remainder: remainder};
  }

  // 2 Abstract Operations (7)
  // 2.1 Type Conversion (7.1)

  // 2.1.4 ToInt64 ( argument )

  // returns {lo, hi}
  function ToInt64(arg) {
    if (Object(arg) === arg)
      arg = Number(arg);
    if (arg instanceof Int64 || arg instanceof Uint64)
      return arg;
    if (typeof arg === 'number') {
      if (arg === 0 || !isFinite(arg))
        return {lo:0, hi:0};
      var int = (arg < 0 ? -1 : 1) * floor(abs(arg));
      var int64bit = int % POW2_64;
      if (int >= POW2_63) int64bit -= POW2_64;

      if (int64bit < 0)
        return negate({lo:-int64bit%POW2_32, hi:-int64bit/POW2_32});
      else
        return {lo:(int64bit%POW2_32)|0, hi:(int64bit/POW2_32)|0};
    }
    if (typeof arg === 'string') {
      // TODO: handle string parsing
      throw TypeError('NYI');
    }
    throw TypeError();
  }

  // 2.1.5 ToUint64 ( argument )

  // returns {lo, hi}
  function ToUint64(arg) {
    if (Object(arg) === arg)
      arg = Number(arg);
    if (arg instanceof Uint64 || arg instanceof Int64)
      return arg;
    if (typeof arg === 'number') {
      if (arg === 0 || !isFinite(arg))
        return {lo:0, hi:0};
      var int = (arg < 0 ? -1 : 1) * floor(abs(arg));
      var int64bit = int % POW2_64;
      return {lo:int64bit|0, hi:(int64bit/POW2_32)|0};
    }
    if (typeof arg === 'string') {
      // TODO: handle string parsing
      throw TypeError('NYI');
    }

    throw TypeError();
  }

  // 7 Int64 Objects

  // 7.1 The Int64 constructor
  // 7.1.1 Int64( [ value ] )

  var SECRET = Symbol();

  function Int64() {
    if (!(this instanceof Int64))
      return arguments.length === 0 ? new Int64() : new Int64(arguments[0]);

    if (arguments.length === 0) {
      this.lo = 0; this.hi = 0;
    } else if (arguments[0] === SECRET) {
      this.lo = arguments[1]|0; this.hi = arguments[2]|0;
    } else {
      var n = ToInt64(arguments[0]);
      this.lo = n.lo; this.hi = n.hi;
    }
    Object.freeze(this);
  }
  function makeInt64(lo, hi) { return new Int64(SECRET, lo, hi); }

  var iZERO = makeInt64(0, 0);
  var iONE = makeInt64(1, 0);

  // 7.2 Properties of the Int64 constructor

  // 7.2.1 Int64.MAX_VALUE
  Object.defineProperty(Int64, 'MAX_VALUE', {
    value: makeInt64(0xFFFFFFFF, 0x7FFFFFFF),
    writable: false, enumerable: false, configurable: true
  });

  // 7.2.2 Int64.MIN_VALUE
  Object.defineProperty(Int64, 'MIN_VALUE', {
    value: makeInt64(0x0, 0x80000000),
    writable: false, enumerable: false, configurable: true
  });

  // 7.2.3 Int64.add( a, b )
  Int64.add = function add(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    var c = uadd(a, b);
    return makeInt64(c.lo, c.hi);
  };

  // 7.2.4 Int64.sub( a, b )
  Int64.sub = function sub(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    var a0 = a.lo >>> 0, a1 = a.hi >>> 0;
    var b0 = b.lo >>> 0, b1 = b.hi >>> 0;

    var c0 = (a0 - b0) >>> 0;
    var r = ((~a0 & b0) | (~(a0 ^ b0) & c0)) >>> 31;
    var c1 = (a1 - b1 - r)|0;
    return makeInt64(c0, c1);
  };

  // 7.2.5 Int64.mul( a, b )
  Int64.mul = function mul(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();

    if (eq(a, iZERO) || eq(b, iZERO))
      return iZERO;

    // TODO: Handle MIN_VALUE which can't be negated
    var an = lt0(a), bn = lt0(b);
    if (an) a = Int64.neg(a);
    if (bn) b = Int64.neg(b);

    var c = umul(makeUint64(a.lo, a.hi), makeUint64(b.lo, b.hi));
    if (an !== bn) c = negate(c);
    return makeInt64(c.lo, c.hi);
  };

  // 7.2.6 Int64.div( a, b )
  Int64.div = function div(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();

    // SPEC ISSUE: Definition for division by zero?
    if (eq(b, iZERO)) throw RangeError('Division by zero');

    // TODO: Handle MIN_VALUE which can't be negated
    var an = lt0(a), bn = lt0(b);
    if (an) a = Int64.neg(a);
    if (bn) b = Int64.neg(b);

    var q = udivrem(makeUint64(a.lo, a.hi), makeUint64(b.lo, b.hi)).quotient;
    if (an !== bn) q = negate(q);
    return makeInt64(q.lo, q.hi);
  };

  // 7.2.7 Int64.mod( a, b )
  Int64.mod = function mod(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();

    // SPEC ISSUE: Definition for division by zero?
    if (eq(b, iZERO)) throw RangeError('Division by zero');

    // TODO: Handle MIN_VALUE which can't be negated
    var an = lt0(a), bn = lt0(b);
    if (an) a = Int64.neg(a);
    if (bn) b = Int64.neg(b);

    var r = udivrem(makeUint64(a.lo, a.hi), makeUint64(b.lo, b.hi)).remainder;
    if (an) r = negate(r);
    return makeInt64(r.lo, r.hi);
  };

  // 7.2.8 Int64.neg( a )
  Int64.neg = function neg(a) {
    if (!(a instanceof Int64)) throw TypeError();
    if (icmp(a, Int64.MIN_VALUE) === 0) return a;
    var n = negate(a);
    return makeInt64(n.lo, n.hi);
  };

  // 7.2.9 Int64.not( a )
  Int64.not = function not(a) {
    if (!(a instanceof Int64)) throw TypeError();
    return makeInt64(~a.lo, ~a.hi);
  };

  // 7.2.10 Int64.and( a, b )
  Int64.and = function and(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return makeInt64(a.lo & b.lo, a.hi & b.hi);
  };

  // 7.2.11 Int64.or( a, b )
  Int64.or = function or(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return makeInt64(a.lo | b.lo, a.hi | b.hi);
  };

  // 7.2.12 Int64.xor( a, b )
  Int64.xor = function xor(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return makeInt64(a.lo ^ b.lo, a.hi ^ b.hi);
  };

  // 7.2.13 Int64.greaterThan( a, b )
  Int64.greaterThan = function greaterThan(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return icmp(a, b) > 0;
  };

  // 7.2.14 Int64.lessThan( a, b )
  Int64.lessThan = function lessThan(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return icmp(a, b) < 0;
  };

  // 7.2.15 Int64.greaterThanOrEqual( a, b )
  Int64.greaterThanOrEqual = function greaterThanOrEqual(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return icmp(a, b) >= 0;
  };

  // 7.2.16 Int64.lessThanOrEqual( a, b )
  Int64.lessThanOrEqual = function lessThanOrEqual(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return icmp(a, b) <= 0;
  };

  // 7.2.17 Int64.compare( a, b )
  Int64.compare = function compare(a, b) {
    if (!(a instanceof Int64 && b instanceof Int64)) throw TypeError();
    return icmp(a, b);
  };

  // 7.2.18 Int64.min( values... )
  Int64.min = function min(values, _) {
    values = Array.from(arguments);
    if (!values.every(function(v) { return v instanceof Int64; })) throw TypeError();

    return values.reduce(function(a, b) {
      return icmp(a, b) < 0 ? a : b;
    }, Int64.MAX_VALUE);
  };

  // 7.2.19 Int64.max( values... )
  Int64.max = function min(values, _) {
    values = Array.from(arguments);
    if (!values.every(function(v) { return v instanceof Int64; })) throw TypeError();

    return values.reduce(function(a, b) {
      return icmp(a, b) > 0 ? a : b;
    }, Int64.MIN_VALUE);
  };

  // 7.2.20 Int64.abs( a )
  Int64.abs = function abs(a) {
    if (!(a instanceof Int64)) throw TypeError();
    if (icmp(a, iZERO) < 0 && icmp(a, Int64.MIN_VALUE) !== 0)
      return Int64.neg(a);
    return a;
  };

  // 7.2.21 Int64.combine( lo, hi )
  Int64.combine = function combine(lo, hi) {
    return makeInt64(lo, hi);
  };

  // 7.2.22 Int64.shiftLeft( value, shifter )
  Int64.shiftLeft = function shiftLeft(value, shifter) {
    if (!(value instanceof Int64)) throw TypeError();
    var shiftValue = shifter >>> 0;
    var shiftCount = shifter % 64;

    if (shiftCount === 0)
      return value;

    if (shiftCount >= 32)
      return makeInt64(0, value.lo << shiftCount - 32);

    return makeInt64(value.lo << shiftCount,
                     (value.hi << shiftCount) | (value.lo >>> (32 - shiftCount)));
  };

  // 7.2.23 Int64.shiftRightArithmetic( value, shifter )
  Int64.shiftRightArithmetic = function shiftRightArithmetic(value, shifter) {
    if (!(value instanceof Int64)) throw TypeError();
    var shiftValue = shifter >>> 0;
    var shiftCount = shifter % 64;

    if (shiftCount === 0)
      return value;

    if (shiftCount >= 32)
      return makeInt64(value.hi >> (shiftCount - 32), value.hi >> 31);

    return makeInt64((value.lo >>> shiftCount) | (value.hi << (32 - shiftCount)),
                     value.hi >> shiftCount);
  };

  // 7.3 Properties of the Int64 Prototype Object

  // 7.3.1 Int64.prototype.valueOf()
  Int64.prototype.valueOf = function valueOf() {
    // non-standard, for debugging
    console.warn('valueOf() called on Int64');
    throw Error();
  };

  // 7.3.2 Int64.prototype.toLocaleString( [ reserved1 [ , reserved2 ] ])

  // 7.3.3 Int64.prototype.toString()

  // SPEC ISSUE: Should take optional base?
  Int64.prototype.toString = function toString() {
    // Non-standard
    var base = arguments.length > 0 ? Number(arguments[0]) : 10;

    var value = this, sign = '';
    if (icmp(value, 0) < 0) {
      value = Int64.neg(value);
      sign = '-';
    }

    var s = '', n, lo = value.lo, hi = value.hi;

    if (base === 2) {
      for (n = 0; n < 32; ++n)
        s = ((lo >> n) & 0x1).toString(base) + s;
      for (n = 0; n < 32; ++n)
        s = ((hi >> n) & 0x1).toString(base) + s;
      return sign + s.replace(/^0+/, '') || '0';
    }

    if (base === 16) {
      for (n = 0; n < 32; n += 4)
        s = ((lo >> n) & 0xF).toString(base) + s;;
      for (n = 0; n < 32; n += 4)
        s = ((hi >> n) & 0xF).toString(base) + s;
      return sign + s.replace(/^0+/, '') || '0';
    }

    return this.toNumber().toString(base);
  };

  // Non-standard
  Int64.prototype.toNumber = function toNumber() {
    //console.warn('Losing precision');
    var n = this;
    if (eq(n, Int64.MIN_VALUE)) return -Math.pow(2,63);
    if (lt0(n)) {
      n = negate(n);
      return -(((n.hi>>>0) * POW2_32) + (n.lo >>> 0));
    }
    return ((n.hi>>>0) * POW2_32) + (n.lo >>> 0);
  };


  // 8 Uint64 Objects

  // 8.1 The Uint64 constructor
  // 8.1.1 Uint64( [ value ] )
  function Uint64() {
    if (!(this instanceof Uint64))
      return arguments.length === 0 ? new Uint64() : new Uint64(arguments[0]);

    if (arguments.length === 0) {
      this.lo = 0; this.hi = 0;
    } else if (arguments[0] === SECRET) { // non-standard
      this.lo = arguments[1] >>> 0; this.hi = arguments[2] >>> 0;
    } else {
      var n = ToUint64(arguments[0]);
      this.lo = n.lo; this.hi = n.hi;
    }
    Object.freeze(this);
  }
  function makeUint64(lo, hi) { return new Uint64(SECRET, lo, hi); }

  var uZERO = makeUint64(0, 0);
  var uONE = makeUint64(1, 0);

  // 8.2 Properties of the Uint64 constructor

  // 8.2.1 Uint64.MAX_VALUE
  Object.defineProperty(Uint64, 'MAX_VALUE', {
    value: makeUint64(0xFFFFFFFF, 0xFFFFFFFF),
    writable: false, enumerable: false, configurable: true
  });

  // 8.2.2 Uint64.MIN_VALUE
  // SPEC ISSUE: "Int64.MIN_VALUE ... tagged as Int64."
  Object.defineProperty(Uint64, 'MIN_VALUE', {
    value: makeUint64(0, 0),
    writable: false, enumerable: false, configurable: true
  });

  // 8.2.3 Uint64.add( a, b )
  Uint64.add = function add(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    var c = uadd(a, b);
    return makeUint64(c.lo, c.hi);
  };

  // "Other function properties of Int64 are added analogously, through compare."

  Uint64.sub = function sub(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    var c = usub(a, b);
    return makeUint64(c.lo, c.hi);
  };

  // 7.2.5 Uint64.mul( a, b )
  Uint64.mul = function mul(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();

    var c = umul(a, b);
    return makeUint64(c.lo, c.hi);
  };

  Uint64.div = function div(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();

    // SPEC ISSUE: Definition for division by zero?
    if (eq(b, iZERO)) throw RangeError('Division by zero');

    var c = udivrem(a, b).quotient;
    return makeUint64(c.lo, c.hi);
  };

  Uint64.mod = function mod(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();

    // SPEC ISSUE: Definition for division by zero?
    if (eq(b, iZERO)) throw RangeError('Division by zero');

    var c = udivrem(a, b).remainder;
    return makeUint64(c.lo, c.hi);
  };

  // SPEC ISSUE: neg doesn't make sense for Uint64

  Uint64.not = function not(a) {
    if (!(a instanceof Uint64)) throw TypeError();
    return makeUint64(~a.lo, ~a.hi);
  };

  Uint64.and = function and(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return makeUint64(a.lo & b.lo, a.hi & b.hi);
  };

  Uint64.or = function or(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return makeUint64(a.lo | b.lo, a.hi | b.hi);
  };

  Uint64.xor = function xor(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return makeUint64(a.lo ^ b.lo, a.hi ^ b.hi);
  };

  Uint64.greaterThan = function greaterThan(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return ucmp(a, b) > 0;
  };

  Uint64.lessThan = function lessThan(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return ucmp(a, b) < 0;
  };

  Uint64.greaterThanOrEqual = function greaterThanOrEqual(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return ucmp(a, b) >= 0;
  };

  Uint64.lessThanOrEqual = function lessThanOrEqual(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return ucmp(a, b) <= 0;
  };

  Uint64.compare = function compare(a, b) {
    if (!(a instanceof Uint64 && b instanceof Uint64)) throw TypeError();
    return ucmp(a, b);
  };

  // 8.2.4 Uint64.min( values... )
  Uint64.min = function min(values, _) {
    values = Array.from(arguments);
    if (!values.every(function(v) { return v instanceof Uint64; })) throw TypeError();

    return values.reduce(function(a, b) {
      return ucmp(a, b) < 0 ? a : b;
    }, Uint64.MAX_VALUE);
    // SPEC ISSUE: "return the largest Int64 value"
  };

  // 8.2.5 Uint64.max( values... )
  Uint64.max = function min(values, _) {
    values = Array.from(arguments);
    if (!values.every(function(v) { return v instanceof Uint64; })) throw TypeError();

    return values.reduce(function(a, b) {
      return ucmp(a, b) > 0 ? a : b;
    }, Uint64.MIN_VALUE);
    // SPEC ISSUE: "return the smallest Int64 value"
  };

  // 8.2.6 Uint64.combine( lo, hi )
  Uint64.combine = function combine(lo, hi) {
    // SPEC ISSUE: "Let hiValue be ToUint32(lo)."
    return makeUint64(lo, hi);
  };

  // 8.2.7 Uint64.shiftLeft( value, shifter )
  Uint64.shiftLeft = function shiftLeft(value, shifter) {
    if (!(value instanceof Uint64)) throw TypeError();
    var shiftValue = shifter >>> 0;
    var shiftCount = shifter % 64;

    if (shiftCount === 0)
      return value;

    if (shiftCount >= 32)
      return makeUint64(0, value.lo << shiftCount - 32);

    return makeUint64(value.lo << shiftCount,
                      (value.hi << shiftCount) | (value.lo >>> (32 - shiftCount)));
  };

  // 8.2.8 Uint64.shiftRightLogical( value, shifter )
  Uint64.shiftRightLogical = function shiftRightLogical(value, shifter) {
    if (!(value instanceof Uint64)) throw TypeError();
    var shiftValue = shifter >>> 0;
    var shiftCount = shifter % 64;

    if (shiftCount === 0)
      return value;

    if (shiftCount >= 32)
      return makeUint64(value.hi >>> (shiftCount - 32), 0);

    return makeUint64((value.lo >>> shiftCount) | (value.hi << (32 - shiftCount)),
                       value.hi >>> shiftCount);
  };

  // 8.2.9 Uint64.clz( value )
  Uint64.clz = function clz(value) {
    if (!(value instanceof Uint64)) throw TypeError();
    return clz64(value);
  };

  // 8.3 Properties of the Uint64 Prototype Object

  // 8.3.1 Uint64.prototype.valueOf()
  Uint64.prototype.valueOf = function valueOf() {
    // non-standard, for debugging
    console.warn('valueOf() called on Uint64');
    throw Error();
  };

  // 8.3.2 Uint64.prototype.toLocaleString( [ reserved1 [ , reserved2 ] ])
  // 8.3.3 Uint64.prototype.toString()

  // SPEC ISSUE: Should take optional base?
  Uint64.prototype.toString = function toString() {
    // Non-standard
    var base = arguments.length > 0 ? Number(arguments[0]) : 10;
    var s = '', n, lo = this.lo, hi = this.hi;

    if (base === 2) {
      for (n = 0; n < 32; ++n)
        s = ((lo >> n) & 0x1).toString(base) + s;
      for (n = 0; n < 32; ++n)
        s = ((hi >> n) & 0x1).toString(base) + s;
      return s.replace(/^0+/, '') || '0';
    }

    if (base === 16) {
      for (n = 0; n < 32; n += 4)
        s = ((lo >> n) & 0xF).toString(base) + s;;
      for (n = 0; n < 32; n += 4)
        s = ((hi >> n) & 0xF).toString(base) + s;
      return s.replace(/^0+/, '') || '0';
    }

    return this.toNumber().toString(base);
  };

  // Non-standard
  Uint64.prototype.toNumber = function toNumber() {
    //console.warn('Losing precision');
    var hi = this.hi >>> 0, lo = this.lo >>> 0;
    return hi * POW2_32 + lo;
  };

  // Export
  global.Int64 = global.Int64 || Int64;
  global.Uint64 = global.Uint64 || Uint64;
}(self));
