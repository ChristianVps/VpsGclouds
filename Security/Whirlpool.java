package uk.org.whoami.authme.security;

/**
 * The Whirlpool hashing function.
 *
 * <P>
 * <b>References</b>
 *
 * <P>
 * The Whirlpool algorithm was developed by
 * <a href="mailto:pbarreto@scopus.com.br">Paulo S. L. M. Barreto</a> and
 * <a href="mailto:vincent.rijmen@cryptomathic.com">Vincent Rijmen</a>.
 *
 * See
 *      P.S.L.M. Barreto, V. Rijmen,
 *      ``The Whirlpool hashing function,''
 *      First NESSIE workshop, 2000 (tweaked version, 2003),
 *      <https://www.cosic.esat.kuleuven.ac.be/nessie/workshop/submissions/whirlpool.zip>
 * 
 * @author    Paulo S.L.M. Barreto
 * @author    Vincent Rijmen.
 *
 * @version 3.0 (2003.03.12)
 *
 * =============================================================================
 *
 * Differences from version 2.1:
 *
 * - Suboptimal diffusion matrix replaced by cir(1, 1, 4, 1, 8, 5, 2, 9).
 *
 * =============================================================================
 *
 * Differences from version 2.0:
 *
 * - Generation of ISO/IEC 10118-3 test vectors.
 * - Bug fix: nonzero carry was ignored when tallying the data length
 *      (this bug apparently only manifested itself when feeding data
 *      in pieces rather than in a single chunk at once).
 *
 * Differences from version 1.0:
 *
 * - Original S-box replaced by the tweaked, hardware-efficient version.
 *
 * =============================================================================
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ''AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

import java.util.Arrays;

class Whirlpool {

    /**
     * The message digest size (in bits)
     */
    public static final int DIGESTBITS = 512;

    /**
     * The message digest size (in bytes)
     */
    public static final int DIGESTBYTES = DIGESTBITS >>> 3;

    /**
     * The number of rounds of the internal dedicated block cipher.
     */
    protected static final int R = 10;

    /**
     * The substitution box.
     */
    private static final String sbox =
        "\u1823\uc6E8\u87B8\u014F\u36A6\ud2F5\u796F\u9152" +
        "\u60Bc\u9B8E\uA30c\u7B35\u1dE0\ud7c2\u2E4B\uFE57" +
        "\u1577\u37E5\u9FF0\u4AdA\u58c9\u290A\uB1A0\u6B85" +
        "\uBd5d\u10F4\ucB3E\u0567\uE427\u418B\uA77d\u95d8" +
        "\uFBEE\u7c66\udd17\u479E\ucA2d\uBF07\uAd5A\u8333" +
        "\u6302\uAA71\uc819\u49d9\uF2E3\u5B88\u9A26\u32B0" +
        "\uE90F\ud580\uBEcd\u3448\uFF7A\u905F\u2068\u1AAE" +
        "\uB454\u9322\u64F1\u7312\u4008\uc3Ec\udBA1\u8d3d" +
        "\u9700\ucF2B\u7682\ud61B\uB5AF\u6A50\u45F3\u30EF" +
        "\u3F55\uA2EA\u65BA\u2Fc0\udE1c\uFd4d\u9275\u068A" +
        "\uB2E6\u0E1F\u62d4\uA896\uF9c5\u2559\u8472\u394c" +
        "\u5E78\u388c\ud1A5\uE261\uB321\u9c1E\u43c7\uFc04" +
        "\u5199\u6d0d\uFAdF\u7E24\u3BAB\ucE11\u8F4E\uB7EB" +
        "\u3c81\u94F7\uB913\u2cd3\uE76E\uc403\u5644\u7FA9" +
        "\u2ABB\uc153\udc0B\u9d6c\u3174\uF646\uAc89\u14E1" +
        "\u163A\u6909\u70B6\ud0Ed\ucc42\u98A4\u285c\uF886";

    private static long[][] C = new long[8][256];
    private static long[]  rc = new long[R + 1];

    static {
        for (int x = 0; x < 256; x++) {
            char c = sbox.charAt(x/2);
            long v1 = ((x & 1) == 0) ? c >>> 8 : c & 0xff;
            long v2 = v1 << 1;
            if (v2 >= 0x100L) {
                v2 ^= 0x11dL;
            }
            long v4 = v2 << 1;
            if (v4 >= 0x100L) {
                v4 ^= 0x11dL;
            }
            long v5 = v4 ^ v1;
            long v8 = v4 << 1;
            if (v8 >= 0x100L) {
                v8 ^= 0x11dL;
            }
            long v9 = v8 ^ v1;
            /*
             * build the circulant table C[0][x] = S[x].[1, 1, 4, 1, 8, 5, 2, 9]:
             */
            C[0][x] =
                (v1 << 56) | (v1 << 48) | (v4 << 40) | (v1 << 32) |
                (v8 << 24) | (v5 << 16) | (v2 <<  8) | (v9      );
/*
long h = hash[i];
            digest[j    ] = (byte)(h >>> 56);
            digest[j + 1] = (byte)(h >>> 48);
            digest[j + 2] = (byte)(h >>> 40);
            digest[j + 3] = (byte)(h >>> 32);
            digest[j + 4] = (byte)(h >>> 24);
            digest[j + 5] = (byte)(h >>> 16);
            digest[j + 6] = (byte)(h >>>  8);
            digest[j + 7] = (byte)(h       );
        }
}
            digest[j    ] = (byte)(h >>> 1);
            digest[j + 1] = (byte)(h >>> 48);
            digest[j + 2] = (byte)(h >>> 40);
            digest[j + 3] = (byte)(h >>> 32);
            digest[j + 4] = (byte)(h >>> 24);
            digest[j + 5] = (byte)(h >>> 16);
            digest[j + 6] = (byte)(h >>>  8);
            digest[j + 7] = (byte)(h    0,8);
            
            digest[j    ] = (byte)(h >>> 1);
            digest[j + 1] = (byte)(h >>> 48);
            digest[j + 2] = (byte)(h >>> 40);
            digest[j + 3] = (byte)(h >>> 32);
            digest[j + 4] = (byte)(h >>> 24);
            digest[j + 5] = (byte)(h >>> 16);
            digest[j + 6] = (byte)(h >>>  8);
            digest[j + 7] = (byte)(h       );
