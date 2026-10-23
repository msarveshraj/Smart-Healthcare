/*
 * Biomedical DSA: Smart Healthcare Algorithms
 * Group 11 - Biomedical Engineering
 * C implementation of:
 * 1. AVL-tree medicine inventory sorted by expiry date
 * 2. Kruskal's and Prim's algorithms for a telemedicine network
 * 3. Linear vs binary search analysis for patient records
 *
 * All included data are synthetic and for academic demonstration only.
 * Compile: gcc -std=c11 -O2 -Wall -Wextra biomedical_dsa_smart_healthcare.c -o biomedical_dsa
 * Run:     ./biomedical_dsa
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <ctype.h>
#include <limits.h>

#define INVENTORY_CAP 100
#define REGISTRY_CAP 2000
#define MAX_NODES 22
#define MAX_EDGES 100
#define INF 1000000000
#define NAME_LEN 80

static void read_line(const char *prompt, char *buf, size_t size) {
    printf("%s", prompt);
    if (!fgets(buf, (int)size, stdin)) { puts(""); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}
static int read_int(const char *prompt, int lo, int hi) {
    char buf[128], *end; long value;
    for (;;) {
        read_line(prompt, buf, sizeof buf);
        value = strtol(buf, &end, 10);
        while (isspace((unsigned char)*end)) end++;
        if (buf[0] && *end == '\0' && value >= lo && value <= hi) return (int)value;
        printf("  Invalid input. Enter a whole number from %d to %d.\n", lo, hi);
    }
}
static int leap_year(int y) { return y % 4 == 0 && (y % 100 != 0 || y % 400 == 0); }
static int days_month(int y, int m) {
    static const int days[] = {31,28,31,30,31,30,31,31,30,31,30,31};
    if (m == 2) return days[1] + leap_year(y);
    return (m >= 1 && m <= 12) ? days[m-1] : 0;
}
static int parse_date(const char *s, int *out) {
    int y, m, d; char extra;
    if (sscanf(s, "%4d-%2d-%2d%c", &y, &m, &d, &extra) != 3) return 0;
    if (y < 2020 || y > 2045 || m < 1 || m > 12 || d < 1 || d > days_month(y,m)) return 0;
    *out = y*10000 + m*100 + d; return 1;
}
static int read_date(const char *prompt) {
    char buf[128]; int d;
    for (;;) { read_line(prompt, buf, sizeof buf); if (parse_date(buf, &d)) return d;
        puts("  Invalid date. Use YYYY-MM-DD (2020-2045), e.g. 2027-03-15."); }
}
static void fmt_date(int d, char *out, size_t n) { snprintf(out, n, "%04d-%02d-%02d", d/10000, d/100%100, d%100); }

/* ---------------- Module 1: AVL medicine inventory ---------------- */
typedef struct AVLNode {
    long long key; char name[NAME_LEN]; int qty, height;
    struct AVLNode *left, *right;
} AVLNode;
typedef struct {
    AVLNode *root; int size, comparisons; int rotations[4];
} Inventory;
static int height(AVLNode *n) { return n ? n->height : 0; }
static int max_int(int a, int b) { return a > b ? a : b; }
static int balance_factor(AVLNode *n) { return n ? height(n->left)-height(n->right) : 0; }
static void update_height(AVLNode *n) { n->height = 1 + max_int(height(n->left), height(n->right)); }
static long long make_key(int date, int batch) { return (long long)date*1000 + batch; }
static void format_key(long long key, char *out, size_t n) {
    char d[16]; fmt_date((int)(key/1000), d, sizeof d); snprintf(out,n,"%s/B%03d",d,(int)(key%1000));
}
static AVLNode *new_node(long long key, const char *name, int qty) {
    AVLNode *n = (AVLNode*)calloc(1,sizeof *n); if (!n) { perror("calloc"); exit(1); }
    n->key=key; strncpy(n->name,name,NAME_LEN-1); n->qty=qty; n->height=1; return n;
}
static AVLNode *rotate_right(AVLNode *y) {
    AVLNode *x=y->left, *t=x->right; x->right=y; y->left=t; update_height(y); update_height(x); return x;
}
static AVLNode *rotate_left(AVLNode *x) {
    AVLNode *y=x->right, *t=y->left; y->left=x; x->right=t; update_height(x); update_height(y); return y;
}
static AVLNode *balance_node(Inventory *inv, AVLNode *n) {
    int b; if (!n) return n; update_height(n); b=balance_factor(n);
    if (b>1) { if (balance_factor(n->left)>=0) { inv->rotations[0]++; return rotate_right(n); }
        inv->rotations[2]++; n->left=rotate_left(n->left); return rotate_right(n); }
    if (b < -1) { if (balance_factor(n->right)<=0) { inv->rotations[1]++; return rotate_left(n); }
        inv->rotations[3]++; n->right=rotate_right(n->right); return rotate_left(n); }
    return n;
}
static AVLNode *find_node(AVLNode *n, long long key) { while(n) { if(key==n->key)return n; n=key<n->key?n->left:n->right; } return NULL; }
static AVLNode *insert_rec(Inventory *inv, AVLNode *n, long long key, const char *name, int qty, int *dup) {
    if (!n) return new_node(key,name,qty);
    inv->comparisons++;
    if(key<n->key)n->left=insert_rec(inv,n->left,key,name,qty,dup);
    else if(key>n->key)n->right=insert_rec(inv,n->right,key,name,qty,dup);
    else { *dup=1; return n; }
    return balance_node(inv,n);
}
static int inv_insert(Inventory *inv,long long key,const char *name,int qty) {
    int dup=0; if(inv->size>=INVENTORY_CAP)return 0;
    inv->root=insert_rec(inv,inv->root,key,name,qty,&dup); if(dup)return -1; inv->size++; return 1;
}
static AVLNode *min_node(AVLNode *n) { if(!n)return NULL; while(n->left)n=n->left; return n; }
static AVLNode *delete_rec(Inventory *inv,AVLNode *n,long long key,int *found) {
    if(!n)return NULL; inv->comparisons++;
    if(key<n->key)n->left=delete_rec(inv,n->left,key,found);
    else if(key>n->key)n->right=delete_rec(inv,n->right,key,found);
    else { AVLNode *s; *found=1;
        if(!n->left){AVLNode *r=n->right; free(n); return r;}
        if(!n->right){AVLNode *l=n->left; free(n); return l;}
        s=min_node(n->right); n->key=s->key; strcpy(n->name,s->name); n->qty=s->qty;
        {int ignored=0; n->right=delete_rec(inv,n->right,s->key,&ignored);}
    }
    return balance_node(inv,n);
}
static int inv_delete(Inventory *inv,long long key) { int found=0; inv->root=delete_rec(inv,inv->root,key,&found); if(found)inv->size--; return found; }
static AVLNode *ceiling_node(AVLNode *n,long long key) { AVLNode *best=NULL; while(n){if(n->key>=key){best=n;n=n->left;}else n=n->right;}return best; }
static void print_batch(AVLNode *n) { char k[32]; format_key(n->key,k,sizeof k); printf("  %-18s %-22s qty=%d\n",k,n->name,n->qty); }
static void inorder_print(AVLNode *n) { if(n){inorder_print(n->left);print_batch(n);inorder_print(n->right);} }
static void range_print(AVLNode *n,long long lo,long long hi,int *count) {
    if(!n)return; if(lo<n->key)range_print(n->left,lo,hi,count);
    if(lo<=n->key&&n->key<=hi){print_batch(n);(*count)++;}
    if(n->key<hi)range_print(n->right,lo,hi,count);
}
static void show_tree(AVLNode *n,int depth) { int i; if(!n)return; show_tree(n->right,depth+1); for(i=0;i<depth;i++)printf("      "); printf("%lld (bf=%+d)\n",n->key,balance_factor(n)); show_tree(n->left,depth+1); }
static int check_avl(AVLNode *n,long long lo,long long hi) { if(!n)return 1; if(n->key<=lo||n->key>=hi||abs(balance_factor(n))>1)return 0; return check_avl(n->left,lo,n->key)&&check_avl(n->right,n->key,hi); }
static void free_tree(AVLNode *n) { if(n){free_tree(n->left);free_tree(n->right);free(n);} }
typedef struct { const char *name,*date; int qty; } Stock;
static const Stock sample_stock[] = {
 {"Paracetamol 500mg","2026-12-15",400},{"Amoxicillin 250mg","2027-03-10",150},{"ORS sachet","2027-08-20",600},
 {"Insulin vial","2026-11-30",80},{"Ceftriaxone 1g","2027-01-25",120},{"Saline 500ml","2028-02-14",300},
 {"Atropine inj","2026-12-02",40},{"Metformin 500mg","2027-06-18",350},{"Adrenaline inj","2027-02-05",60},
 {"Ibuprofen 400mg","2027-09-09",280},{"Heparin inj","2026-11-12",50},{"Salbutamol inhaler","2027-04-22",90},
 {"Pantoprazole 40mg","2027-10-01",200},{"Diazepam inj","2027-05-30",35},{"Ondansetron inj","2026-12-15",110},
 {"Dopamine inj","2027-07-07",45},{"Gentamicin inj","2028-01-19",130},{"Lignocaine 2%","2027-11-25",75},
 {"Vitamin K inj","2028-04-03",55},{"Cetirizine 10mg","2027-12-12",500},{"Furosemide inj","2027-03-10",65},{"Aspirin 75mg","2028-06-28",450}
};
static void load_stock(Inventory *inv) { size_t i; for(i=0;i<sizeof sample_stock/sizeof sample_stock[0];i++){int d;parse_date(sample_stock[i].date,&d);inv_insert(inv,make_key(d,(int)i+1),sample_stock[i].name,sample_stock[i].qty);} }
static void module1(Inventory *inv) {
    for(;;){int c; puts("\n--- MODULE 1: AVL medicine inventory by expiry date ---"); puts("1 Load sample stock  2 Insert batch  3 Delete batch  4 Search batch"); puts("5 Range search  6 Nearest expiry  7 Remove expired stock  8 Inorder listing"); puts("9 Display AVL tree  10 Statistics  0 Back"); c=read_int("Choice: ",0,10); if(!c)return;
        if(c==1){if(inv->size)puts("Inventory is not empty; sample not loaded.");else{load_stock(inv);printf("Loaded %d batches. Height=%d\n",inv->size,height(inv->root));}}
        else if(c==2){char name[NAME_LEN];int d,b,q,r;read_line("Medicine name: ",name,sizeof name);if(!name[0]){puts("Name cannot be empty.");continue;}d=read_date("Expiry date (YYYY-MM-DD): ");b=read_int("Batch no. (1-999): ",1,999);q=read_int("Quantity (1-100000): ",1,100000);r=inv_insert(inv,make_key(d,b),name,q);puts(r==1?"Inserted.":r==0?"Inventory full.":"Duplicate expiry/batch.");}
        else if(c==3||c==4){int d,b;AVLNode *n;if(!inv->root){puts("Inventory is empty.");continue;}d=read_date("Expiry date: ");b=read_int("Batch no. (1-999): ",1,999);if(c==3)puts(inv_delete(inv,make_key(d,b))?"Deleted.":"Batch not found.");else{n=find_node(inv->root,make_key(d,b));if(n)print_batch(n);else puts("Batch not found.");}}
        else if(c==5){int d1=read_date("From date: "),d2=read_date("To date: "),count=0;if(d1>d2){puts("From date is after To date.");continue;}range_print(inv->root,make_key(d1,0),make_key(d2,999),&count);printf("%d batch(es).\n",count);}
        else if(c==6){AVLNode *m=min_node(inv->root),*n;int d;if(!m){puts("Inventory is empty.");continue;}printf("Soonest expiry: ");print_batch(m);d=read_date("Nearest expiry on/after date: ");n=ceiling_node(inv->root,make_key(d,0));if(n)print_batch(n);else puts("No stock expires on or after that date.");}
        else if(c==7){int d=read_date("Remove all stock expiring before: "),removed=0;for(;;){AVLNode *m=min_node(inv->root);if(!m||(int)(m->key/1000)>=d)break;print_batch(m);inv_delete(inv,m->key);removed++;}printf("%d batch(es) removed.\n",removed);}
        else if(c==8){if(!inv->root)puts("Inventory is empty.");else inorder_print(inv->root);}
        else if(c==9){if(!inv->root)puts("(tree is empty)");else show_tree(inv->root,0);}
        else printf("size=%d height=%d rotations LL/RR/LR/RL=%d/%d/%d/%d comparisons=%d AVL-valid=%s\n",inv->size,height(inv->root),inv->rotations[0],inv->rotations[1],inv->rotations[2],inv->rotations[3],inv->comparisons,check_avl(inv->root,-1,LLONG_MAX)?"YES":"NO");
    }
}

/* ---------------- Module 2: Kruskal vs Prim ---------------- */
typedef struct {int u,v,cost;} Edge;
typedef struct {char names[MAX_NODES][12];int n,m;Edge e[MAX_EDGES];} Network;
static const Edge sample_edges[] = {{0,6,53},{0,9,15},{0,14,65},{0,19,46},{1,3,24},{1,7,38},{1,18,14},{2,9,5},{3,12,49},{3,16,29},{4,6,76},{4,7,44},{4,14,61},{4,17,45},{5,6,56},{5,8,55},{5,19,28},{6,8,39},{8,14,30},{8,15,73},{8,18,75},{8,21,17},{9,10,43},{9,20,78},{10,14,33},{10,20,52},{11,21,9},{12,13,64},{12,19,79},{13,20,10},{13,21,8},{14,16,70},{14,21,7},{18,20,62}};
static void init_network(Network *net){int i;memset(net,0,sizeof *net);net->n=MAX_NODES;strcpy(net->names[0],"DH");for(i=1;i<MAX_NODES;i++)snprintf(net->names[i],12,"PHC-%02d",i);net->m=(int)(sizeof sample_edges/sizeof sample_edges[0]);memcpy(net->e,sample_edges,sizeof sample_edges);}
static int edge_cmp(const void *a,const void *b){const Edge *x=a,*y=b;if(x->cost!=y->cost)return x->cost-y->cost;if(x->u!=y->u)return x->u-y->u;return x->v-y->v;}
typedef struct {int parent[MAX_NODES],rank[MAX_NODES],finds;} DSU;
static void dsu_init(DSU *d,int n){int i;d->finds=0;for(i=0;i<n;i++){d->parent[i]=i;d->rank[i]=0;}}
static int dsu_find(DSU *d,int x){int root=x;d->finds++;while(d->parent[root]!=root)root=d->parent[root];while(d->parent[x]!=root){int next=d->parent[x];d->parent[x]=root;x=next;}return root;}
static void dsu_union(DSU *d,int a,int b){if(d->rank[a]<d->rank[b]){int t=a;a=b;b=t;}d->parent[b]=a;if(d->rank[a]==d->rank[b])d->rank[a]++;}
typedef struct {Edge chosen[MAX_NODES];int count,total,connected,comparisons,finds;} MST;
static MST kruskal(Network *net){MST r={0};Edge sorted[MAX_EDGES];DSU d;int i;memcpy(sorted,net->e,(size_t)net->m*sizeof(Edge));qsort(sorted,(size_t)net->m,sizeof(Edge),edge_cmp);dsu_init(&d,net->n);for(i=0;i<net->m;i++){int a=dsu_find(&d,sorted[i].u),b=dsu_find(&d,sorted[i].v);r.comparisons++;if(a!=b){dsu_union(&d,a,b);r.chosen[r.count++]=sorted[i];r.total+=sorted[i].cost;if(r.count==net->n-1)break;}}r.connected=(r.count==net->n-1);r.finds=d.finds;return r;}
static MST prim(Network *net){MST r={0};int w[MAX_NODES][MAX_NODES],key[MAX_NODES],par[MAX_NODES],used[MAX_NODES]={0},i,j;for(i=0;i<net->n;i++){key[i]=INF;par[i]=-1;for(j=0;j<net->n;j++)w[i][j]=INF;}for(i=0;i<net->m;i++){Edge e=net->e[i];w[e.u][e.v]=w[e.v][e.u]=e.cost;}key[0]=0;for(i=0;i<net->n;i++){int best=-1;for(j=0;j<net->n;j++)if(!used[j]){r.comparisons++;if(best<0||key[j]<key[best])best=j;}if(best<0||key[best]==INF)break;used[best]=1;if(par[best]>=0){Edge e={par[best],best,key[best]};r.chosen[r.count++]=e;r.total+=e.cost;}for(j=0;j<net->n;j++)if(!used[j]){r.comparisons++;if(w[best][j]<key[j]){key[j]=w[best][j];par[j]=best;}}}r.connected=(r.count==net->n-1);return r;}
static void print_mst(Network *net,MST r,const char *label){int i;printf("\n%s selected edges:\n",label);for(i=0;i<r.count;i++)printf("  %-7s - %-7s cost Rs %d lakh\n",net->names[r.chosen[i].u],net->names[r.chosen[i].v],r.chosen[i].cost);printf("Edges=%d Total=Rs %d lakh %s\n",r.count,r.total,r.connected?"(spanning tree)":"(disconnected: spanning forest/tree partial)");}
static void module2(Network *net){for(;;){int c;puts("\n--- MODULE 2: Telemedicine network optimization ---");puts("1 Show network  2 Run Kruskal  3 Run Prim  4 Compare algorithms  5 Add link  6 Reset network  0 Back");c=read_int("Choice: ",0,6);if(!c)return;if(c==1){int i;printf("%d centres, %d links (synthetic costs in Rs lakh)\n",net->n,net->m);for(i=0;i<net->m;i++){Edge e=net->e[i];printf("%-7s - %-7s %d\n",net->names[e.u],net->names[e.v],e.cost);}}
else if(c==2){MST r=kruskal(net);print_mst(net,r,"Kruskal");printf("Sort uses C library qsort; union-find calls=%d\n",r.finds);}
else if(c==3){MST r=prim(net);print_mst(net,r,"Prim");printf("Array comparisons=%d\n",r.comparisons);}
else if(c==4){MST k=kruskal(net),p=prim(net);printf("Kruskal: cost=%d, edges=%d, find calls=%d\nPrim: cost=%d, edges=%d, comparisons=%d\nSame total cost: %s\n",k.total,k.count,k.finds,p.total,p.count,p.comparisons,k.total==p.total?"YES":"NO");}
else if(c==5){int u=read_int("From node (0=DH, 1-21=PHC): ",0,net->n-1),v=read_int("To node: ",0,net->n-1),cost=read_int("Cost (Rs lakh, 1-1000): ",1,1000),i,dup=0;if(u==v){puts("Self-link not allowed.");continue;}for(i=0;i<net->m;i++)if((net->e[i].u==u&&net->e[i].v==v)||(net->e[i].u==v&&net->e[i].v==u))dup=1;if(dup)puts("Link already exists.");else if(net->m>=MAX_EDGES)puts("Link capacity reached.");else{net->e[net->m++]=(Edge){u,v,cost};puts("Link added.");}}
else {init_network(net);puts("Sample network restored.");}}
}

/* ---------------- Module 3: patient record searching ---------------- */
typedef struct {int ids[REGISTRY_CAP];char ward[REGISTRY_CAP][12];int n;} Registry;
static int linear_search(const int *a,int n,int key,int *cmp){int i;*cmp=0;for(i=0;i<n;i++){(*cmp)++;if(a[i]==key)return i;}return -1;}
static int binary_search(const int *a,int n,int key,int *cmp){int lo=0,hi=n-1;*cmp=0;while(lo<=hi){int mid=lo+(hi-lo)/2;(*cmp)++;if(a[mid]==key)return mid;if(a[mid]<key)lo=mid+1;else hi=mid-1;}return -1;}
static int valid_pid(const char *s){size_t i;if(strlen(s)!=5||s[0]=='0')return 0;for(i=0;s[i];i++)if(!isdigit((unsigned char)s[i]))return 0;return 1;}
static void load_registry(Registry *r){static const char *wards[]={"ICU","OPD","CARD","ORTHO","PED"};int i;r->n=25;for(i=0;i<r->n;i++){r->ids[i]=10000+37*i+(i*i)%11;strcpy(r->ward[i],wards[i%5]);}}
static int registry_add(Registry *r,int pid,const char *ward){int i;if(r->n>=REGISTRY_CAP)return 0;for(i=0;i<r->n;i++)if(r->ids[i]==pid)return -1;i=r->n;while(i>0&&r->ids[i-1]>pid){r->ids[i]=r->ids[i-1];strcpy(r->ward[i],r->ward[i-1]);i--;}r->ids[i]=pid;strncpy(r->ward[i],ward,11);r->ward[i][11]='\0';r->n++;return 1;}
static void module3(Registry *r){for(;;){int c;puts("\n--- MODULE 3: Linear vs binary search on patient records ---");puts("1 Load sample records  2 Show records  3 Add record  4 Compare searches  5 Run size analysis  6 Complexity summary  0 Back");c=read_int("Choice: ",0,6);if(!c)return;
if(c==1){load_registry(r);printf("Loaded %d synthetic patient records.\n",r->n);}
else if(c==2){int i;if(!r->n)puts("Registry is empty.");for(i=0;i<r->n;i++)printf("[%3d] ID %d  %s\n",i,r->ids[i],r->ward[i]);}
else if(c==3){char s[80],ward[12];int pid,res;read_line("New 5-digit patient ID: ",s,sizeof s);if(!valid_pid(s)){puts("Invalid ID: enter exactly 5 digits, not starting with 0.");continue;}pid=atoi(s);read_line("Ward code (default OPD): ",ward,sizeof ward);if(!ward[0])strcpy(ward,"OPD");res=registry_add(r,pid,ward);puts(res==1?"Record added.":res==0?"Registry full.":"Duplicate ID.");}
else if(c==4){char s[80];int pid,idx1,idx2,c1,c2;read_line("Patient ID to find: ",s,sizeof s);if(!valid_pid(s)){puts("Invalid patient ID.");continue;}if(!r->n){puts("Load records first.");continue;}pid=atoi(s);idx1=linear_search(r->ids,r->n,pid,&c1);idx2=binary_search(r->ids,r->n,pid,&c2);printf("Linear: %s, %d comparisons\n",idx1>=0?"found":"not found",c1);printf("Binary: %s, %d comparisons\n",idx2>=0?"found":"not found",c2);}
else if(c==5){int sizes[]={100,500,1000,5000,10000,50000},si;puts(" n       linear worst   binary worst   linear avg successful   binary avg successful");for(si=0;si<6;si++){int n=sizes[si],*a=(int*)malloc((size_t)n*sizeof(int)),i,cl,cb;double sl=0,sb=0;for(i=0;i<n;i++)a[i]=1000+2*i;for(i=0;i<n;i+=n/100?n/100:1){linear_search(a,n,a[i],&cl);binary_search(a,n,a[i],&cb);sl+=cl;sb+=cb;}linear_search(a,n,a[n-1]+1,&cl);binary_search(a,n,a[n-1]+1,&cb);printf("%-7d %-14d %-14d %-22.1f %.2f\n",n,cl,cb,sl/(n/(n/100?n/100:1)+1),sb/(n/(n/100?n/100:1)+1));free(a);}}
else puts("Linear search: best O(1), average/worst O(n). Binary search: best O(1), average/worst O(log n); requires sorted data.");}}

/* ---------------- Main ---------------- */
int main(void){Inventory inv={0};Network net;Registry reg={0};init_network(&net);for(;;){int c;puts("\n====== BIOMEDICAL DSA: SMART HEALTHCARE ALGORITHMS ======");puts("1 Medicine inventory (AVL tree)\n2 Telemedicine network (Kruskal vs Prim)\n3 Patient record search (linear vs binary)\n0 Exit");c=read_int("Choice: ",0,3);if(c==0)break;if(c==1)module1(&inv);else if(c==2)module2(&net);else module3(&reg);}free_tree(inv.root);puts("Goodbye.");return 0;}
