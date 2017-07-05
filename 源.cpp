#include<iostream>
#include<cstring>
#include<string>
#include<map>
#include<vector>
#include<utility>
#include<fstream>
#include<mutex>
#include<cstdlib>
#include<thread>
#include<condition_variable>
#include<atomic>

using namespace std;
const int maxn = 1 << 22;
unsigned char st[maxn] = { 0 };
int reg[34] = { 0 };
const int dob[4] = { 1,1 << 8,1 << 16,1 << 24 };
const string p[35] = { "$zero","$at","$v0","$v1","$a0","$a1","$a2","$a3","$t0","$t1","$t2","$t3","$t4","$t5","$t6","$t7",
"$s0","$s1","$s2","$s3","$s4","$s5","$s6","$s7","$t8","$t9","$k0","$k1","$gp","$sp","$fp","$ra","$hi","$lo","$s8" };
map<string, int> pb;
const string clist[61] = {
	".align",".ascii",".asciiz",".byte",".half",".word",".space",".data",".text",//9
	"add","addu","addiu","sub","subu","mul","mulu","div","divu","xor","xoru","neg","negu","rem","remu","li",//16
	"seq","sge","sgt","sle","slt","sne",//6
	"b","beq","bne","ble","bge","bgt","blt","beqz","bnez","blez","bgez","bgtz","bltz","j","jr","jal","jalr",//17
	"la","lb","lh","lw",//4
	"sb","sh","sw",//3
	"move","mfhi","mflo",//3
	"nop","syscall",//2
	"main"
};
bool ready[6];
int usingreg[34] = { 0 };
mutex con_lock[6];
condition_variable cv[6];
atomic<bool> finish[6] = { false };
bool conlock[6] = { 0 };
mutex uc;
mutex _lock[6];
bool stall[6] = { 0 };
bool haltlock=false;
bool readed[6] = { false };
int halt;
typedef unsigned long long ull;
typedef long long ll;
struct token {
	string labtoken;
	int op;
	vector<string> optoken;
	token() :op(-1) {}
	void clear() {
		op = -1;
		labtoken = "";
		optoken.clear();
	}
};
struct temp {
	int a[4];
	int op;
	temp() { op = a[0] = a[1] = a[2] = a[3] = -1; }
	temp &operator =(const temp&rhs) {
		if (this == &rhs) return *this;
		for (int i = 0;i < 4;++i)
			a[i] = rhs.a[i];
		op = rhs.op;
		return *this;
	}
};
bool dat = true;
token command[10000];
int cnt = 0;
int pointer = 0;
int pc = 0;
int npc = 0;
temp tmp[6];
typedef pair<int, bool> T;
map<string, T> lab;
map<char, char> cvt;
int npc_modifier = 0;
int s2i(const string &s) {
	int n = 0;
	int t, y;
	if (s[0] != '-') {
		t = 0;y = 1;
	}
	else { t = 1; y = -1; }
	for (int i = t;i < s.length();++i) {
		n = n * 10 + s[i] - 48;
	}
	n *= y;
	return n;
}
int id(const string &s) {
	if (s[0] != '$') throw;
	if (s[1] <= '9'&&s[1] >= '0') {
		if (s.length()>2 && s[2] <= '9'&&s[2] >= '0')
			return ((s[1] - 48) * 10 + s[2] - 48);
		else return (s[1] - 48);
	}
	else {
		return pb[s];
	}
}
int offcov1(const string &s) {
	string t = "";
	for (int i = 0;s[i] != '(';++i) {
		t += s[i];
	}
	return s2i(t);
}
int offcov2(const string &s) {
	string t = "";
	int i = 0;
	while (s[i] != '(') ++i;
	++i;
	while (s[i] != ')') t += s[i++];
	return id(t);
}
void convert(const string &s, int k) {
	unsigned int n = s2i(s);
	for (int i = 0;i < k;++i) {
		int x = n % 256;
		n /= 256;
		st[pointer++] = x;
	}
}

bool align(int k, int t = 0) {
	int n = 0;
	string s = command[k].optoken[0];
	n = s2i(s);
	int x = (1 << n);
	if (pointer % x == 0) return false;
	else pointer = pointer + x - pointer%x;
	return false;
}

bool ascii(int n, int t = 0) {
	string s = command[n].optoken[0];
	bool ve = false;
	for (int i = 0;i < s.length();++i) {
		if (s[i] != '\"' && !ve && s[i] != '\\')
			st[pointer++] = s[i];
		else if (ve) {
			st[pointer++] = cvt[s[i]];
			ve = false;
		}
		else if (s[i] == '\\') ve = true;
	}
	return false;
}

bool asciiz(int n, int t = 0) {
	string s = command[n].optoken[0];
	bool ve = false;
	for (int i = 0;i < s.length();++i) {
		if (s[i] != '\"' && !ve && s[i] != '\\')
			st[pointer++] = s[i];
		else if (ve) {
			st[pointer++] = cvt[s[i]];
			ve = false;
		}
		else if (s[i] == '\\') ve = true;
	}
	st[pointer++] = '\0';
	return false;
}

bool byte(int n, int t = 0) {
	for (int i = 0;i < command[n].optoken.size();++i) {
		convert(command[n].optoken[i], 1);
	}
	return false;
}

bool half(int n, int t = 0) {
	for (int i = 0;i < command[n].optoken.size();++i) {
		convert(command[n].optoken[i], 2);
	}
	return false;
}

bool word(int n, int t = 0) {
	for (int i = 0;i < command[n].optoken.size();++i) {
		convert(command[n].optoken[i], 4);
	}
	return false;
}

bool space(int k, int t = 0) {
	string s = command[k].optoken[0];
	pointer += s2i(s);
	return false;
}

bool datum(int n, int t = 0) {
	dat = true;
	return false;
}

bool text(int n, int t = 0) {
	dat = false;
	return false;
}

bool add(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool addu(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (unsigned int)tmp[3].a[1] + (unsigned int)tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool addiu(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (unsigned int)tmp[3].a[1] + (unsigned int)tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sub(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] -= tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool subu(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (unsigned int)tmp[3].a[1] - (unsigned int)tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool mul(int n, int t) {
	if (t == 3) {
		if (tmp[3].a[0] < 0) {
			ll t;
			t = (ll)tmp[3].a[1] * (ll)tmp[3].a[2];
			ll m = (1 << 32);
			tmp[3].a[2] = (int)t;
			tmp[3].a[1] = (int)(t >> 32);
		}
		else {
			tmp[3].a[1] *= tmp[3].a[2];
		}
	}
	if (t == 5) {
		if (tmp[t].a[0] < 0) {
			reg[32] = tmp[t].a[1];
			reg[33] = tmp[t].a[2];
			--usingreg[32]; --usingreg[33];
		}
		else {
			reg[tmp[t].a[0]] = tmp[t].a[1];
			--usingreg[tmp[5].a[0]];
		}
	}
	return false;
}

bool mulu(int n, int t) {
	if (t == 3) {
		if (tmp[3].a[0] < 0) {
			ull t;
			t = (ull)tmp[3].a[1] * (ull)tmp[3].a[2];
			ull m = (1 << 32);
			tmp[3].a[2] = (int)t;
			tmp[3].a[1] = (int)(t >> 32);
		}
		else {
			tmp[3].a[1] = (unsigned int)tmp[3].a[1] * (unsigned int)tmp[3].a[2];
		}
	}
	if (t == 5) {
		if (tmp[t].a[0] < 0) {
			reg[32] = tmp[t].a[1];
			reg[33] = tmp[t].a[2];
			--usingreg[32]; --usingreg[33];
		}
		else { reg[tmp[t].a[0]] = tmp[t].a[1];--usingreg[tmp[5].a[0]]; }
	}
	return false;
}

bool dive(int n, int t) {
	if (t == 3) {
		if (tmp[3].a[0] < 0) {
			ll t;
			t = (ll)tmp[3].a[1] / (ll)tmp[3].a[2];
			ll m = (ll)tmp[3].a[1] % (ll)tmp[3].a[2];
			tmp[3].a[2] = t;
			tmp[3].a[1] = m;
		}
		else {
			tmp[3].a[1] /= tmp[3].a[2];
		}
	}
	if (t == 5) {
		if (tmp[t].a[0] < 0) {
			reg[32] = tmp[t].a[1];
			reg[33] = tmp[t].a[2];
			--usingreg[32];--usingreg[33];
		}
		else {
			reg[tmp[t].a[0]] = tmp[t].a[1];--usingreg[tmp[5].a[0]];
		}
	}
	return false;
}

bool divu(int n, int t) {
	if (t == 3) {
		if (tmp[3].a[0] < 0) {
			ull t;
			t = (ull)tmp[3].a[1] / (ull)tmp[3].a[2];
			ull m = (ull)tmp[3].a[1] % (ull)tmp[3].a[2];
			tmp[3].a[2] = t;
			tmp[3].a[1] = m;
		}
		else {
			tmp[3].a[1] = (unsigned int)tmp[3].a[1] / (unsigned int)tmp[3].a[2];
		}
	}
	if (t == 5) {
		if (tmp[t].a[0] < 0) {
			reg[32] = tmp[t].a[1];
			reg[33] = tmp[t].a[2];
			--usingreg[32];--usingreg[33];
		}
		else {
			reg[tmp[t].a[0]] = tmp[t].a[1];--usingreg[tmp[5].a[0]];
		}
	}
	return false;
}

bool xors(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] ^= tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool xoru(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (unsigned int)tmp[3].a[1] ^ (unsigned int)tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool neg(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = -tmp[3].a[1];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool negu(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = -tmp[3].a[1];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool rem(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] %= tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool remu(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (unsigned int)tmp[3].a[1] % (unsigned int)tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool li(int n, int t) {
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool seq(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] == tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sge(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] >= tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sgt(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] > tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sle(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] <= tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool slt(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] < tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sne(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] != tmp[3].a[2] ? 1 : 0);
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool b(int n, int t) {
	if (t == 3) return true;
	if (t == 5) { 
		npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
	}
	return false;
}

bool beq(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] == tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bne(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] != tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bge(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] >= tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool ble(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] <= tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bgt(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] > tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool blt(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] < tmp[3].a[2] ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool beqz(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] == 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bnez(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] != 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bgez(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] >= 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool blez(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] <= 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bgtz(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] > 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool bltz(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] = (tmp[3].a[1] < 0 ? 1 : 0);
		if (tmp[3].a[1] == 1) return true;
	}
	if (t == 5) {
		if (tmp[5].a[1] == 1) {
			npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
		}
	}
	return false;
}

bool j(int n, int t) {
	if (t == 3) return true;
	if (t == 5) {
		npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
	}
	return false;
}

bool jr(int n, int t) {
	if (t == 3) return true;
	if (t == 5) {
		npc = tmp[5].a[0]; --npc_modifier;memset(usingreg,0,sizeof(usingreg));
	}
	return false;
}

bool jal(int n, int t) {
	if (t == 3) return true;
	if (t == 5) {
		npc = tmp[5].a[0]; 
		--npc_modifier;
		reg[31] = tmp[t].a[1];
		memset(usingreg, 0, sizeof(usingreg));
	}
	return false;
}

bool jalr(int n, int t) {
	if (t == 3) return true;
	if (t == 5) {
		npc = tmp[5].a[0];
		--npc_modifier;
		reg[31] = tmp[t].a[1];
		memset(usingreg, 0, sizeof(usingreg));
	}
	return false;
}

bool la(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool lb(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		tmp[t].a[1] = st[tmp[t].a[1]];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool lh(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		tmp[t].a[2] = 0;
		for (int i = 0;i < 2;++i) {
			tmp[t].a[2] += st[tmp[t].a[1] + i] * dob[i];
		}
		tmp[t].a[1] = tmp[t].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool lw(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		tmp[t].a[2] = 0;
		for (int i = 0;i < 4;++i) {
			tmp[t].a[2] += st[tmp[t].a[1] + i] * dob[i];
		}
		tmp[t].a[1] = tmp[t].a[2];
	}
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool sb(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		unsigned int tp = tmp[t].a[0];
		for (int i = 0;i < 1;++i) {
			st[tmp[t].a[1] + i] = tp % 256;
			tp /= 256;
		}
	}
	return false;
}

bool sh(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		unsigned int tp = tmp[t].a[0];
		for (int i = 0;i < 2;++i) {
			st[tmp[t].a[1] + i] = tp % 256;
			tp /= 256;
		}
	}
	return false;
}

bool sw(int n, int t) {
	if (t == 3) {
		tmp[3].a[1] += tmp[3].a[2];
	}
	if (t == 4) {
		unsigned int tp = tmp[t].a[0];
		for (int i = 0;i < 4;++i) {
			st[tmp[t].a[1] + i] = tp % 256;
			tp /= 256;
		}
	}
	return false;
}

bool move(int n, int t) {
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool mfhi(int n, int t) {
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool mflo(int n, int t) {
	if (t == 5) {
		reg[tmp[5].a[0]] = tmp[5].a[1];
		--usingreg[tmp[5].a[0]];
	}
	return false;
}

bool nop(int n, int t) { return false; }

bool syscall(int n, int t) {
	if (tmp[t].a[0] == 10) {
		haltlock=true;
	}
	if (tmp[t].a[0] == 17) {
		haltlock=true;
		halt = tmp[t].a[1];
	}
	if (t == 3 && tmp[t].a[0] == 1) {
		cout << tmp[t].a[1];
	}
	if (t == 4 && tmp[t].a[0] == 4) {
		int tp = tmp[t].a[1];
		while (st[tp] != '\0') cout << st[tp++];
	}
	if (tmp[t].a[0] == 5) {
		if (t == 3) cin >> tmp[t].a[1];
		if (t == 5) { reg[2] = tmp[t].a[1]; }
	}
	if (tmp[t].a[0] == 9) {
		if (t == 3) {
			tmp[t].a[2] = pointer;pointer += tmp[t].a[1];
		}
		if (t == 5) { reg[2] = tmp[t].a[2]; }
	}
	if (t == 4 && tmp[t].a[0] == 8) {
		char c;
		c = cin.get();
		while (c == '\n' || c == '\r' || c == '\0') c = cin.get();
		int i = 1;
		while (c != '\n'&&c != '\0' && i< tmp[t].a[2]) {
			st[tmp[t].a[1]++] = c;
			c = cin.get();
			++i;
		}
		st[tmp[t].a[1]] = 0;
	}
	if (t == 5)--usingreg[2];
	return false;
}

bool(*func[60])(int n, int t) = {
	align,ascii,asciiz,byte,half,word,space,datum,text,
	add,addu,addiu,sub,subu,mul,mulu,dive,divu,xors,xoru,neg,negu,rem,remu,li,
	seq,sge,sgt,sle,slt,sne,
	b,beq,bne,ble,bge,bgt,blt,beqz,bnez,blez,bgez,bgtz,bltz,j,jr,jal,jalr,
	la,lb,lh,lw,
	sb,sh,sw,
	move,mfhi,mflo,
	nop,syscall
};
/*".align", ".ascii", ".asciiz", ".byte", ".half", ".word", ".space", ".data", ".text",//9
"add", "addu", "addiu", "sub", "subu", "mul", "mulu", "div", "divu", "xor", "xoru", "neg", "negu", "rem", "remu", "li",//16
"seq", "sge", "sgt", "sle", "slt", "sne",//6
"b", "beq", "bne", "ble", "bge", "bgt", "blt", "beqz", "bnez", "blez", "bgez", "bgtz", "bltz", "j", "jr", "jal", "jalr",//17
"la", "lb", "lh", "lw",//4
"sb", "sh", "sw",//3
"move", "mfhi", "mflo",//3
"nop", "syscall",//2
"main"*/

bool deal(char* s, int n) {
	string t = "";
	command[n].clear();
	int i = 0;
	while (s[i] == ' ' || s[i] == '\t') ++i;
	if (i >= strlen(s)) return false;
	if (s[i] == '#') return false;
	while ((s[i] != ' '&&s[i] != ':'&&s[i] != '\t') && i < strlen(s)) t += s[i++];
	for (int j = 0;j < 61;++j) {
		if (clist[j] == t) { command[n].op = j;break; }
	}
	int k = command[n].op;
	if (k < 0) {
		command[n].labtoken = t;
		T x(pointer, dat);
		T y(n, dat);
		if (dat) lab.insert(make_pair(t, x));
		else lab.insert(make_pair(t, y));
		return false;
	}
	while (i < strlen(s)) {
		t = "";
		while ((s[i] == ' ' || s[i] == ',' || s[i] == '\t') && i < strlen(s)) ++i;
		if (s[i] != '\"')
			while (s[i] != ' '&&s[i] != ','&&s[i] != '\t'&&i < strlen(s)) t += s[i++];
		else {
			++i;
			while (s[i] != '\"'&&i < strlen(s)) t += s[i++];
		}
		command[n].optoken.push_back(t);
	}
	if (k == 7) { dat = true;return false; }
	if (k == 8) { dat = false;return false; }
	if (k == 60) { pc = n;return false; }
	return true;
}
token x,c;
mutex pclock;
bool modpc = false;
void IF() {
	while (!haltlock) {
		unique_lock<mutex> lck1(con_lock[1]);
		while (!ready[1])
			cv[1].wait(lck1);
		while (!readed[2]) {}
		pclock.lock();
		modpc = true;
		pc = npc;
		npc = pc + 1;
		c = command[pc];
		pclock.unlock();
		finish[1] = true;
		ready[1] = false;
	}
}

void IDDP() {
	while (!haltlock) {
		unique_lock<mutex> lck2(con_lock[2]);
		while (!ready[2])
			cv[2].wait(lck2);
		if (!stall[2]) {
			x = c;
			modpc = false;
			readed[2] = true;
		}
		bool dat_haz = false;
		int k;
		if (x.op >= 9 && x.op <= 19 || x.op <= 30 && x.op >= 22 && x.op != 24) {
			if (x.optoken.size() == 2) {
				tmp[2].a[0] = -1;
				for (int i = 0;i < 2;++i) {
					if (x.optoken[i][0] == '$') {
						k = id(x.optoken[i]);
						if (usingreg[k]) {
							dat_haz = true;break;
						}
						tmp[2].a[i + 1] = reg[k];
					}
					else tmp[2].a[i + 1] = s2i(x.optoken[i]);
				}
				if (!dat_haz) {
					++usingreg[32];++usingreg[33];
				}
			}
			else if (x.optoken.size() == 3) {
				tmp[2].a[0] = id(x.optoken[0]);
				for (int i = 1;i < 3;++i) {
					if (x.optoken[i][0] == '$') {
						k = id(x.optoken[i]);
						if (usingreg[k]) {
							dat_haz = true;break;
						}
						tmp[2].a[i] = reg[k];
					}
					else tmp[2].a[i] = s2i(x.optoken[i]);
				}
				if (!dat_haz)
					++usingreg[tmp[2].a[0]];
			}
		}
		if (x.op >= 20 && x.op <= 21 || x.op == 24) {
			tmp[2].a[0] = id(x.optoken[0]);
			for (int i = 1;i < 2;++i) {
				if (x.optoken[i][0] == '$') {
					k = id(x.optoken[i]);
					if (usingreg[k]) {
						dat_haz = true;break;
					}
					tmp[2].a[i] = reg[k];
				}
				else tmp[2].a[i] = s2i(x.optoken[i]);
			}
			if (!dat_haz)
				++usingreg[tmp[2].a[0]];
		}
		if (x.op >= 31 && x.op <= 44) {
			tmp[2].a[0] = lab[x.optoken.back()].first;
			for (int i = 0;i < x.optoken.size() - 1;++i) {
				if (x.optoken[i][0] == '$') {
					k = id(x.optoken[i]);
					if (usingreg[k]) {
						dat_haz = true;break;
					}
					tmp[2].a[i + 1] = reg[k];
				}
				else tmp[2].a[i + 1] = s2i(x.optoken[i]);
			}
		}
		if (x.op == 45) {
			k = id(x.optoken[0]);
			if (usingreg[k]) {
				dat_haz = true;
			}
			else
				tmp[2].a[0] = reg[k];
		}
		if (x.op == 46) {
			tmp[2].a[0] = lab[x.optoken[0]].first;
			pclock.lock();
			if (modpc)
				tmp[2].a[1] = pc;
			else
				tmp[2].a[1] = pc + 1;
			pclock.unlock();
			++usingreg[31];
		}
		if (x.op == 47) {
			k = id(x.optoken[0]);
			if (usingreg[k]) {
				dat_haz = true;
			}
			if (!dat_haz) {
				tmp[2].a[0] = reg[k];
				pclock.lock();
				if (modpc)
					tmp[2].a[1] = pc;
				else 	tmp[2].a[1] = pc + 1;
				pclock.unlock();
				++usingreg[31];
			}
		}
		if (x.op <= 51 && x.op >= 48) {
			tmp[2].a[0] = id(x.optoken[0]);
			char c = x.optoken[1][0];
			if (c >= '0'&&c <= '9' || c == '-' || c == '(') {
				tmp[2].a[1] = offcov1(x.optoken[1]);
				k = offcov2(x.optoken[1]);
				if (usingreg[k]) {
					dat_haz = true;
				}
				else
					tmp[2].a[2] = reg[k];
			}
			else { tmp[2].a[1] = 0;tmp[2].a[2] = lab[x.optoken.back()].first; }
			if (!dat_haz)
				++usingreg[tmp[2].a[0]];
		}
		if (x.op <= 54 && x.op >= 52) {
			k = id(x.optoken[0]);
			if (usingreg[k]) {
				dat_haz = true;
			}
			if (!dat_haz) {
				tmp[2].a[0] = reg[k];
				char c = x.optoken[1][0];
				if (c >= '0'&&c <= '9' || c == '-' || c == '(') {
					tmp[2].a[1] = offcov1(x.optoken[1]);
					k = offcov2(x.optoken[1]);
					if (usingreg[k]) {
						dat_haz = true;
					}
					else
						tmp[2].a[2] = reg[k];
				}
				else { tmp[2].a[1] = 0;tmp[2].a[2] = lab[x.optoken.back()].first; }
			}
		}
		if (x.op == 55) {
			tmp[2].a[0] = id(x.optoken[0]);
			k = id(x.optoken[1]);
			if (usingreg[k]) {
				dat_haz = true;
			}
			else {
				tmp[2].a[1] = reg[k];
				++usingreg[tmp[2].a[0]];
			}
		}
		if (x.op == 56) {
			tmp[2].a[0] = id(x.optoken[0]);
			if (usingreg[32]) {
				dat_haz = true;
			}
			else {
				tmp[2].a[1] = reg[32];
				++usingreg[tmp[2].a[0]];
			}
		}
		if (x.op == 57) {
			tmp[2].a[0] = id(x.optoken[0]);
			if (usingreg[33]) {
				dat_haz = true;
			}
			else {
				tmp[2].a[1] = reg[33];
				++usingreg[tmp[2].a[0]];
			}
		}
		if (x.op == 59) {
			if (usingreg[2] || usingreg[4] || usingreg[5]) {
				dat_haz = true;
			}
			else {
				tmp[2].a[0] = reg[2];
				tmp[2].a[1] = reg[4];
				tmp[2].a[2] = reg[5];
				++usingreg[2];
			}
		}
		if (dat_haz) {
			stall[2] = true;
		}
		else {
			stall[2] = false;
			tmp[2].op = x.op;
		}
		while (!readed[3]) {}
		_lock[3].lock();
		tmp[3] = tmp[2];
		_lock[3].unlock();
		tmp[2] = tmp[1];
		finish[2] = true;
		ready[2] = false;
	}
}

void EXE() {
	while (!haltlock) {
		unique_lock<mutex> lck3(con_lock[3]);
		while (!ready[3])
			cv[3].wait(lck3);
		bool h = true;
		int op = tmp[3].op;
		_lock[3].lock();
		if (op >= 0) {
			if (func[op](-1, 3)) {
				++npc_modifier;
			}
		}
		while (!readed[4]) {}
		_lock[4].lock();
		tmp[4] = tmp[3];
		_lock[4].unlock();
		readed[3] = true;
		_lock[3].unlock();
		finish[3] = true;
		ready[3] = false;
	}
}


void MA() {
	while (!haltlock) {
		unique_lock<mutex> lck4(con_lock[4]);
		while (!ready[4]) cv[4].wait(lck4);
		int op = tmp[4].op;
		_lock[4].lock();
		if (op >= 0) {
			func[op](-1, 4);
		}
		while (!readed[5]){  }
		_lock[5].lock();
		tmp[5] = tmp[4];
		_lock[5].unlock();
		readed[4] = true;
		_lock[4].unlock();
		finish[4] = true;
		ready[4] = false;
	}
}

void WB() {
	while (!haltlock) {
		unique_lock<mutex> lck5(con_lock[5]);
		while(!ready[5]) cv[5].wait(lck5);
		int op = tmp[5].op;
		_lock[5].lock();
		if (op >= 0) {
			func[op](-1, 5);
		}
		readed[5] = true;
		_lock[5].unlock();
		finish[5] = true;
		ready[5] = false;
	}
}
int main(int argc, char *argv[]) {
	halt = 0;
	ios::sync_with_stdio(false);
	cin.tie(0);
	cout.tie(0);
	x.op = -1;
	char s[500];
	reg[29] = maxn - 1;
	cvt['n'] = '\n';
	cvt['b'] = '\b';
	cvt['a'] = '\a';
	cvt['f'] = '\f';
	cvt['r'] = '\r';
	cvt['t'] = '\t';
	cvt['v'] = '\v';
	cvt['\\'] = '\\';
	cvt['\''] = '\'';
	cvt['\"'] = '\"';
	cvt['\?'] = '\?';
	cvt['0'] = '\0';
	pb["s8"] = 30;
	for (int i = 0;i < 34;++i) {
		pb[p[i]] = i;
	}
	ifstream infile(argv[1]);
	while (infile.getline(s, 500)) {
		bool h = deal(s, cnt);
		if (h) {
			if (dat && command[cnt].op >= 0 && command[cnt].op<9) {
				func[command[cnt].op](cnt, 0);
			}
			++cnt;
		}
	}
	cnt += 5;
	npc = pc;
	thread wb(WB);
	thread ma(MA);
	thread exe(EXE);
	thread iddp(IDDP);
	thread iF(IF);
	wb.detach();
	ma.detach();
	exe.detach();
	iddp.detach();
	iF.detach();
	int k;
	while (!haltlock) {
		if (npc_modifier) {
			k = 3;
		}
		else if (stall[2]) k = 2;
		else k = 1;
		for (int i=1;i<5;++i)
			ready[i] = false;
		unique_lock<mutex> lck[6];
		for (int i = 1;i <= 5;++i)
			lck[i] = unique_lock<mutex>(con_lock[i]);
		for (int i = 5;i >= k;--i) {
			ready[i] = true;
			cv[i].notify_all();
		}
		for (int i = 5;i >= k;--i)
			lck[i].unlock();
		for (int i = k;i <= 5;++i) {
			while (!finish[i]) {  }
		}
		for (int i = 1;i <= 5;++i) {
			readed[i] = false;finish[i] = false;
		}
		if (npc_modifier) {
			stall[2] = false;
			x.op = -1;
			c.op = -1;
			tmp[2].op = -1;
			tmp[3].op = -1;
		}
	}
	return halt;
	/*	while (npc < cnt) {
	try {
	IF();
	IDDP(c, pc);
	tmp[3] = tmp[2];
	EXE(tmp[3].op);
	tmp[4] = tmp[3];
	MA(tmp[4].op);
	tmp[5] = tmp[4];
	WB(tmp[5].op);
	}
	catch (halt x) {
	if (x.h) return x.val;
	else return 0;
	}
	catch (data_haz) {
	for (int i = 4;i > 2;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	MA(tmp[4].op);
	for (int i = 4;i > 3;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	for (int i = 5;i > 2;--i) tmp[i].op = -1;
	IDDP(c, pc);
	IF();
	}
	catch (con_haz) {
	for (int i = 4;i > 2;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	MA(tmp[4].op);
	for (int i = 4;i > 3;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	for (int i = 5;i > 0;--i) tmp[i].op = -1;
	c.op = -1;
	}
	}*/
	/*	while (npc < cnt) {
	for (int i = 4;i > 0;--i) {
	tmp[i + 1] = tmp[i];
	}
	try {
	WB(tmp[5].op);
	MA(tmp[4].op);
	EXE(tmp[3].op);
	IDDP(c, pc);
	IF();
	}
	catch (halt x) {
	if (x.h) return x.val;
	else return 0;
	}
	catch (data_haz) {
	for (int i = 4;i > 2;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	MA(tmp[4].op);
	for (int i = 4;i > 3;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	for (int i = 5;i > 2;--i) tmp[i].op = -1;
	IDDP(c, pc);
	IF();
	}
	catch (con_haz) {
	for (int i = 4;i > 2;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	MA(tmp[4].op);
	for (int i = 4;i > 3;--i) {
	tmp[i + 1] = tmp[i];
	}
	WB(tmp[5].op);
	for (int i = 5;i > 0;--i) tmp[i].op = -1;
	c.op = -1;
	}
	}
	*/
	return 0;
}
