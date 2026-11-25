module

public import Erdos272.Certificates.Staircase249Data.Part07

@[expose] public section

namespace JSP233.Staircase249Data
open JSP233.Staircase249Counts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def potential244 (i : Nat) : Int := staircasePotential i 244

def potential245 (i : Nat) : Int := staircasePotential i 245

def potential246 (i : Nat) : Int := staircasePotential i 246

def potential247 (i : Nat) : Int := staircasePotential i 247

def potential248 (i : Nat) : Int := staircasePotential i 248

def potential249 (i : Nat) : Int := staircasePotential i 249

def potentialLookup (r i : Nat) : Int := (if r < 128 then (if r < 64 then (if r < 32 then (if r < 16 then (if r < 8 then (if r < 4 then (if r < 2 then (if r < 1 then potential000 i else potential001 i) else (if r < 3 then potential002 i else potential003 i)) else (if r < 6 then (if r < 5 then potential004 i else potential005 i) else (if r < 7 then potential006 i else potential007 i))) else (if r < 12 then (if r < 10 then (if r < 9 then potential008 i else potential009 i) else (if r < 11 then potential010 i else potential011 i)) else (if r < 14 then (if r < 13 then potential012 i else potential013 i) else (if r < 15 then potential014 i else potential015 i)))) else (if r < 24 then (if r < 20 then (if r < 18 then (if r < 17 then potential016 i else potential017 i) else (if r < 19 then potential018 i else potential019 i)) else (if r < 22 then (if r < 21 then potential020 i else potential021 i) else (if r < 23 then potential022 i else potential023 i))) else (if r < 28 then (if r < 26 then (if r < 25 then potential024 i else potential025 i) else (if r < 27 then potential026 i else potential027 i)) else (if r < 30 then (if r < 29 then potential028 i else potential029 i) else (if r < 31 then potential030 i else potential031 i))))) else (if r < 48 then (if r < 40 then (if r < 36 then (if r < 34 then (if r < 33 then potential032 i else potential033 i) else (if r < 35 then potential034 i else potential035 i)) else (if r < 38 then (if r < 37 then potential036 i else potential037 i) else (if r < 39 then potential038 i else potential039 i))) else (if r < 44 then (if r < 42 then (if r < 41 then potential040 i else potential041 i) else (if r < 43 then potential042 i else potential043 i)) else (if r < 46 then (if r < 45 then potential044 i else potential045 i) else (if r < 47 then potential046 i else potential047 i)))) else (if r < 56 then (if r < 52 then (if r < 50 then (if r < 49 then potential048 i else potential049 i) else (if r < 51 then potential050 i else potential051 i)) else (if r < 54 then (if r < 53 then potential052 i else potential053 i) else (if r < 55 then potential054 i else potential055 i))) else (if r < 60 then (if r < 58 then (if r < 57 then potential056 i else potential057 i) else (if r < 59 then potential058 i else potential059 i)) else (if r < 62 then (if r < 61 then potential060 i else potential061 i) else (if r < 63 then potential062 i else potential063 i)))))) else (if r < 96 then (if r < 80 then (if r < 72 then (if r < 68 then (if r < 66 then (if r < 65 then potential064 i else potential065 i) else (if r < 67 then potential066 i else potential067 i)) else (if r < 70 then (if r < 69 then potential068 i else potential069 i) else (if r < 71 then potential070 i else potential071 i))) else (if r < 76 then (if r < 74 then (if r < 73 then potential072 i else potential073 i) else (if r < 75 then potential074 i else potential075 i)) else (if r < 78 then (if r < 77 then potential076 i else potential077 i) else (if r < 79 then potential078 i else potential079 i)))) else (if r < 88 then (if r < 84 then (if r < 82 then (if r < 81 then potential080 i else potential081 i) else (if r < 83 then potential082 i else potential083 i)) else (if r < 86 then (if r < 85 then potential084 i else potential085 i) else (if r < 87 then potential086 i else potential087 i))) else (if r < 92 then (if r < 90 then (if r < 89 then potential088 i else potential089 i) else (if r < 91 then potential090 i else potential091 i)) else (if r < 94 then (if r < 93 then potential092 i else potential093 i) else (if r < 95 then potential094 i else potential095 i))))) else (if r < 112 then (if r < 104 then (if r < 100 then (if r < 98 then (if r < 97 then potential096 i else potential097 i) else (if r < 99 then potential098 i else potential099 i)) else (if r < 102 then (if r < 101 then potential100 i else potential101 i) else (if r < 103 then potential102 i else potential103 i))) else (if r < 108 then (if r < 106 then (if r < 105 then potential104 i else potential105 i) else (if r < 107 then potential106 i else potential107 i)) else (if r < 110 then (if r < 109 then potential108 i else potential109 i) else (if r < 111 then potential110 i else potential111 i)))) else (if r < 120 then (if r < 116 then (if r < 114 then (if r < 113 then potential112 i else potential113 i) else (if r < 115 then potential114 i else potential115 i)) else (if r < 118 then (if r < 117 then potential116 i else potential117 i) else (if r < 119 then potential118 i else potential119 i))) else (if r < 124 then (if r < 122 then (if r < 121 then potential120 i else potential121 i) else (if r < 123 then potential122 i else potential123 i)) else (if r < 126 then (if r < 125 then potential124 i else potential125 i) else (if r < 127 then potential126 i else potential127 i))))))) else (if r < 192 then (if r < 160 then (if r < 144 then (if r < 136 then (if r < 132 then (if r < 130 then (if r < 129 then potential128 i else potential129 i) else (if r < 131 then potential130 i else potential131 i)) else (if r < 134 then (if r < 133 then potential132 i else potential133 i) else (if r < 135 then potential134 i else potential135 i))) else (if r < 140 then (if r < 138 then (if r < 137 then potential136 i else potential137 i) else (if r < 139 then potential138 i else potential139 i)) else (if r < 142 then (if r < 141 then potential140 i else potential141 i) else (if r < 143 then potential142 i else potential143 i)))) else (if r < 152 then (if r < 148 then (if r < 146 then (if r < 145 then potential144 i else potential145 i) else (if r < 147 then potential146 i else potential147 i)) else (if r < 150 then (if r < 149 then potential148 i else potential149 i) else (if r < 151 then potential150 i else potential151 i))) else (if r < 156 then (if r < 154 then (if r < 153 then potential152 i else potential153 i) else (if r < 155 then potential154 i else potential155 i)) else (if r < 158 then (if r < 157 then potential156 i else potential157 i) else (if r < 159 then potential158 i else potential159 i))))) else (if r < 176 then (if r < 168 then (if r < 164 then (if r < 162 then (if r < 161 then potential160 i else potential161 i) else (if r < 163 then potential162 i else potential163 i)) else (if r < 166 then (if r < 165 then potential164 i else potential165 i) else (if r < 167 then potential166 i else potential167 i))) else (if r < 172 then (if r < 170 then (if r < 169 then potential168 i else potential169 i) else (if r < 171 then potential170 i else potential171 i)) else (if r < 174 then (if r < 173 then potential172 i else potential173 i) else (if r < 175 then potential174 i else potential175 i)))) else (if r < 184 then (if r < 180 then (if r < 178 then (if r < 177 then potential176 i else potential177 i) else (if r < 179 then potential178 i else potential179 i)) else (if r < 182 then (if r < 181 then potential180 i else potential181 i) else (if r < 183 then potential182 i else potential183 i))) else (if r < 188 then (if r < 186 then (if r < 185 then potential184 i else potential185 i) else (if r < 187 then potential186 i else potential187 i)) else (if r < 190 then (if r < 189 then potential188 i else potential189 i) else (if r < 191 then potential190 i else potential191 i)))))) else (if r < 224 then (if r < 208 then (if r < 200 then (if r < 196 then (if r < 194 then (if r < 193 then potential192 i else potential193 i) else (if r < 195 then potential194 i else potential195 i)) else (if r < 198 then (if r < 197 then potential196 i else potential197 i) else (if r < 199 then potential198 i else potential199 i))) else (if r < 204 then (if r < 202 then (if r < 201 then potential200 i else potential201 i) else (if r < 203 then potential202 i else potential203 i)) else (if r < 206 then (if r < 205 then potential204 i else potential205 i) else (if r < 207 then potential206 i else potential207 i)))) else (if r < 216 then (if r < 212 then (if r < 210 then (if r < 209 then potential208 i else potential209 i) else (if r < 211 then potential210 i else potential211 i)) else (if r < 214 then (if r < 213 then potential212 i else potential213 i) else (if r < 215 then potential214 i else potential215 i))) else (if r < 220 then (if r < 218 then (if r < 217 then potential216 i else potential217 i) else (if r < 219 then potential218 i else potential219 i)) else (if r < 222 then (if r < 221 then potential220 i else potential221 i) else (if r < 223 then potential222 i else potential223 i))))) else (if r < 240 then (if r < 232 then (if r < 228 then (if r < 226 then (if r < 225 then potential224 i else potential225 i) else (if r < 227 then potential226 i else potential227 i)) else (if r < 230 then (if r < 229 then potential228 i else potential229 i) else (if r < 231 then potential230 i else potential231 i))) else (if r < 236 then (if r < 234 then (if r < 233 then potential232 i else potential233 i) else (if r < 235 then potential234 i else potential235 i)) else (if r < 238 then (if r < 237 then potential236 i else potential237 i) else (if r < 239 then potential238 i else potential239 i)))) else (if r < 248 then (if r < 244 then (if r < 242 then (if r < 241 then potential240 i else potential241 i) else (if r < 243 then potential242 i else potential243 i)) else (if r < 246 then (if r < 245 then potential244 i else potential245 i) else (if r < 247 then potential246 i else potential247 i))) else (if r < 252 then (if r < 250 then (if r < 249 then potential248 i else potential249 i) else Int.ofNat 0) else Int.ofNat 0))))))

def suffix000 (i : Nat) : Int := staircaseSuffix i 0

def suffix001 (i : Nat) : Int := staircaseSuffix i 1

def suffix002 (i : Nat) : Int := staircaseSuffix i 2

def suffix003 (i : Nat) : Int := staircaseSuffix i 3

def suffix004 (i : Nat) : Int := staircaseSuffix i 4

def suffix005 (i : Nat) : Int := staircaseSuffix i 5

def suffix006 (i : Nat) : Int := staircaseSuffix i 6

def suffix007 (i : Nat) : Int := staircaseSuffix i 7

def suffix008 (i : Nat) : Int := staircaseSuffix i 8

def suffix009 (i : Nat) : Int := staircaseSuffix i 9

def suffix010 (i : Nat) : Int := staircaseSuffix i 10

def suffix011 (i : Nat) : Int := staircaseSuffix i 11

def suffix012 (i : Nat) : Int := staircaseSuffix i 12

def suffix013 (i : Nat) : Int := staircaseSuffix i 13

def suffix014 (i : Nat) : Int := staircaseSuffix i 14

def suffix015 (i : Nat) : Int := staircaseSuffix i 15

def suffix016 (i : Nat) : Int := staircaseSuffix i 16

def suffix017 (i : Nat) : Int := staircaseSuffix i 17

def suffix018 (i : Nat) : Int := staircaseSuffix i 18

def suffix019 (i : Nat) : Int := staircaseSuffix i 19

def suffix020 (i : Nat) : Int := staircaseSuffix i 20

end JSP233.Staircase249Data
