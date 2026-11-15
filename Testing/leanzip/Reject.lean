import Riscv.Frontx.Machine
import Orig
-- Each lean-zip kernel, unmodified (Testing/leanzip/Orig.lean), given to `frontx_compile`; the messages are the
-- rejection table of Testing/notes/LEANZIP_SURVEY.md section 7.  Run: Testing/leanzip/run.sh reject
open Proven Proven.Frontx Orig
set_option maxHeartbeats 400000
frontx_compile Adler32.Native.updateBytes
frontx_compile Adler32.Native.adler32
frontx_compile Adler32.Spec.updateByte
frontx_compile Crc32.Spec.crcByteTable
frontx_compile Crc32.Native.updateBytes
frontx_compile Crc32.Native.crc32
frontx_compile ZipCommon.BitReader.readBits
frontx_compile ZipCommon.BitReader.readBits.go
frontx_compile Zip.Native.readBitsFast
frontx_compile Zip.Native.readBitsFast.go
frontx_compile Zip.Native.InflateBuf.decodeSym
frontx_compile Zip.Native.InflateBuf.takeBits
frontx_compile Zip.Native.InflateBuf.walkTree
frontx_compile Zip.Native.countMatchGo
frontx_compile Zip.Native.Inflate.copyLoopGo
frontx_compile Zip.Native.Inflate.copyLoop
frontx_compile Zip.Native.Inflate.decodeStored
frontx_compile ByteArray.fillDouble
frontx_compile ByteArray.copyWithin
frontx_compile ByteArray.extendWithin
