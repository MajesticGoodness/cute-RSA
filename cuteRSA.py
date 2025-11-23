import random

# Euclid to the rescue. Thanks for the algorithm big guy.
def gcd (remainder_0, remainder_1) :
    
    while remainder_0 % remainder_1 != 0 :
        remainder_next = remainder_0 % remainder_1
        remainder_0 = remainder_1
        remainder_1 = remainder_next
    
    return remainder_1

# I wish I knew more functional programming because this algorithm lends itself to that paradigm. 
# prev(prev(prev t)) looks ugly but it's quite intuitive.
def extended_gcd (remainder_0, remainder_1) :
    
    s_0 = 1
    s_1 = 0
    t_0 = 0
    t_1 = 1
    prev_quotient = remainder_0 // remainder_1

    while remainder_0 % remainder_1 != 0:
        remainder_next = remainder_0 % remainder_1 # the ith remainder (begins at i = 2)

        # next iteration we're doing remainder_0 + 1 % remainder_1 + 1, so we need to update them.
        remainder_0 = remainder_1
        remainder_1 = remainder_next

        # as above, we increment each s and t as we iterate.
        current_s = s_0 - prev_quotient * s_1
        s_0 = s_1
        s_1 = current_s

        current_t = t_0 - prev_quotient * t_1
        t_0 = t_1
        t_1 = current_t

        # the next iteration needs to use this iteration's quotient, so we calculate it last
        prev_quotient = remainder_0 // remainder_1

    return (s_1, t_1)

# helper function for the miller-rabin test primality test.
# expects an odd number as input
def prime_factorization (n) :
    
    # subtract 1 to make n even and prepare parameters u and r

    n = n - 1

    # factor out the two's first.
    u = 0 # the exponent on the two's

    while n % 2 == 0 :
        n = n // 2
        u = u + 1
    
    # the odd component is whatever we have leftover.
    r = n
    return (u, r)

def sq_and_mul (base, expon, modulus) :
    # return value
    result = base

    # convert exponent to binary
    binExpon = bin(expon)

    # disregard the first bit, as well as the '0b' prefix.
    startIndex = 3
    for currentBit in binExpon[startIndex:] :

        # square
        result = (result * result) % modulus

        # multiply only if bit is turned on
        if currentBit == '1' :
            result = (result * base ) % modulus
    
    return result

# adopted directly from Paar's textbook
def prime_test (prime, security) :
    
    # where u is the number of two's of (prime - 1) and r is the leftover odd factor
    (u, r) = prime_factorization(prime)

    # repeat the test up to the number of iterations set by the security parameter
    # to rule out liar's to the test with a high degree of certainty
    for i in range(security) :
        # choose a random base.
        # if we choose enough random bases for the digit length of our number,
        # we can be almost certain of the test being accurate.
        a = random.randint(2, prime - 2)

        # raise the base to the last halved (prime - 1).
        # if our prime candidate is 221, then this would be halved as follows:
        # (221 - 1) = 220
        # 220 / 2 = 110
        # 110 / 2 = 55
        # at this point we can't divide further, so this is the 'last half'
        # and it's the first exponent we raise our base to, so r = 55 and u = 2
        z = sq_and_mul(a, r, prime)

        # if the left hand side is true, then this number is a fermat witness
        # if the right hand side is true, then it's a witness to this test.
        # in either case, we should choose another base to test until we've 
        # exhausted our security iterations
        if (z != 1 and z != prime - 1) :

            j = 1
            # iterate back up our 'halves' by effectively multiplying r by 2 each iteration.
            # multiplying z by itself accomplishes the same task.
            # if we run into (prime - 1) then we know this base a witness to the test and should try another. 
            while j <= u - 1 and z != prime - 1 :
                z = z * z % prime
                # we know that 1 should only appear after a 1 or a prime - 1 appears.
                # but, if we're in this loop, then it means that the prior number was neither a 1, nor a prime - 1.
                # so, the test fails and the number must be composite.
                #if z == 1 : 
                    #return False
                j = j + 1
            
            # in this algorithm we don't even need to check the end of the sequence, since we know
            # that the number prior to the end of the sequence must be prime - 1. this is why we
            # iterate only up to u - 1, instead of u itself. we're only concerned that the second to last
            # number in the sequence is prime - 1, since if it isn't, then the number is composite.
            if z != prime - 1 :
                return False
            
            # as an example, the following sequence is produced with prime = 561, a = 484, r = 35, u = 4
            # 121, 55, 220, 154, 1 (presumably)
            # we inserted a 1 at the end, but this algorithm skips that step
            # and instead produces 121, 55, 220, 154 as the sequence since it knows that
            # number preceding 1 at the end of the sequence must be prime - 1.
            # since that number isn't prime - 1 (i.e., 560),
            # the algorithm correctly detects that 561 is indeed composite.

    return True

def gib_prime (bitLength, security_param) :
    cutePair = []
    primesFound = 0

    while primesFound != 2 :

        # if bitLength = 512, then gib primes between 2 ^ 511 and (2 ^ 512) - 1.
        # 512 bit numbers start at 2 ^ (512 - 1) and end at at (2 ^ 512) - 1
        # not cryptographically secure! just for demonstration purposes

        prime_candidate = random.randint(2 ** (bitLength - 1), 2 ** bitLength - 1)
        
        if prime_test(prime_candidate, security_param) :

            cutePair.append(prime_candidate)
            primesFound = primesFound + 1
    
    return cutePair

def gib_modulo_n (cutePair) :
    #p = cutePair[0]
    #q = cutePair[1]
    p, q = cutePair
    return p * q

def gib_phi (cutePair) :
    #p = cutePair[0]
    #q = cutePair[1]
    p, q = cutePair
    return (p - 1) * (q - 1)

def gib_e (phi) :
    e = random.randint(2, phi - 1) # might be a good idea to not include 1
    
    while gcd(e, phi) != 1 :
        e = random.randint(2, phi - 1)
    
    return e

def gib_d (phi, e) :
    s, t = extended_gcd(phi, e)

    if t < 0 :
        t = t + phi

    return t

def generateKeys(bitLength, security_param) :
    cutePair = gib_prime(bitLength, security_param)
    phi = gib_phi(cutePair)
    n = gib_modulo_n(cutePair)
    e = gib_e(phi)
    d = gib_d(phi, e)

    print("Here are your keys :)\n\n" +
          "Public Key:\n" + 
          "n = ", n, '\n'
          "e = ", e, '\n'
          "Private Key:\n" +
          "d = ", d)
    
    return n, e, d

def encrypt (plaintext, n, e) :
    return sq_and_mul(plaintext, e, n)

def decrypt (cipherText, d, n) :
    return sq_and_mul(cipherText, d, n)

def main() :
    security_param = 5 # good default for 500 bit longish primes 
    bitLength = 512
    randomPlainText = random.randint(0, 1000)
    n, e, d = generateKeys(bitLength, security_param)
    
    print("\nRandomly selected ", randomPlainText, " as our plaintext.")
    
    cipherText = encrypt(randomPlainText, n, e)
    print("Ciphertext: ", cipherText)
    
    decrypted = decrypt(cipherText, d, n)
    print("Decrypted result: ", decrypted)

main()

#prime_test(211, 5)
#sq_and_mul(76, 57, 211)