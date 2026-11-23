# GsXFuscator V0.6 — Güvenli Cloudflare Dağıtımı

Bu paket, verilen `d.zip` projesindeki **web üzerinden motorun kopyalanabilmesi** sorununu kaynak kodu kamuya açık web sayfasından çıkararak azaltır. V0.6 arayüzü, profil/settings, dosya seçimi, Luau tespiti, sonuç görüntüleme, kopyalama ve indirme işlevleri korunur. Genel developer dokümantasyonu ve motor bileşenleri herkese açık web çıktısından çıkarılmıştır.

## Önemli: mümkün olan ve olmayan koruma

Bir tarayıcıya gösterilen HTML, CSS, JavaScript ve ekranda görünen içerik tamamen saklanamaz. `view-source`, DevTools, ağ kayıtları ve ekran kopyalama engellenemez. İstemcide çalışan obfuscator motorunun kopyalanmasını engellemenin güvenilir yolu onu **istemciye hiç göndermemektir**. Bu pakette çalışan *derleyici kodu ve Lua modülleri* özel Python servisinde kalır; Cloudflare tarafına yalnızca genel kullanıcı arayüzü ve korumalı API aktarım kodu yüklenir. Görsel arayüz yine kopyalanabilir. İstenirse Cloudflare Access ile arayüz ve API yalnızca yetkili kullanıcılarla sınırlandırılabilir.

## Mimari

```
Tarayıcı (154 KB arayüz; kaynak Lua ve çıktı yerelde saklanmaz)
        | POST /api/build  [HTTPS, aynı origin]
        v
Cloudflare Pages Function   VEYA   Cloudflare Worker
        | Bearer GSX_BUILD_TOKEN (sadece sunucuda saklanır)
        v
Ayrı HTTPS özel Python backend (Lupa / Lua 5.4 / V0.6 motoru)
        | Lua kodunu derler, yanıtı geri döndürür
        v
Tarayıcı (Lua çıktısını Copy / Download)
```

**Tek başına `.pages.dev` / Workers statik hosting yeterli değildir.** Bu sürümde korumalı derleme için çalışan ayrı bir backend şarttır. Backend kurulmadan sayfa açılır fakat `/api/build` 503 döner. Cloudflare Workers içine Python `lupa` derleyicisi koyulduğu iddia edilmez.

## Dizinler

- `pages/`: **Cloudflare Pages** proje kökü. Sadece `pages/public/` statik yayınlanır ve `pages/functions/api/build.js` Functions olarak çalışır.
- `worker/`: **Cloudflare Workers** proje kökü. `worker/assets/` statik yayınlanır, `worker/worker.js` API'yi çalıştırır.
- `private-backend/`: **gizli sunucu kodu**. Asla Pages `public/` veya Workers `assets/` içine kopyalamayın.
- `ui-src/`, `tools/`: UI kaynakları ve güvenli yeniden oluşturma aracı. Bunlar da web sitesinde yayınlanmaz.
- `tests/`: statik kod sızıntısı ve edge API doğrulama testleri.

## 1) Özel backend'i çalıştır

Python 3.12 ve `lupa==2.8` (Lua 5.4) gerekir. Başka bir VPS, Container host veya özel sunucuda:

```sh
cd private-backend
pip install -r web/requirements.txt
export GSX_BUILD_TOKEN="$(openssl rand -hex 32)"
python web/service.py --origin --host 127.0.0.1 --port 8787
```

Sunucunuzda `GSX_BUILD_TOKEN` değerini bir **secret** olarak kaydedin. Bu değeri Cloudflare tarafındaki secret ile aynı yapın. Backend yalnızca Bearer token kabul eder. Backend'in HTTP portunu doğrudan internete açmayın; TLS veren ters proxy aracılığıyla örneğin `https://compiler.sizinalanadiniz.com` adresine yayınlayın. Worker/Pages tarafından erişilebilen HTTPS uç noktası olmalıdır.

Docker ile:

```sh
cd private-backend
docker build -t gsx-private .
docker run --rm --name gsx-private -p 127.0.0.1:8787:8787 \
  -e GSX_BUILD_TOKEN="<sunucunuzdaki_gercek_gizli_deger>" gsx-private
```

Örnek Caddy yapılandırması `private-backend/Caddyfile.example` içindedir. Kendi domaininiz, DNS/TLS ve güvenlik kurallarınız gerekir. **Tokeni hiçbir statik JS/HTML dosyasına yazmayın.** Python servisinde kaynak ve çıktı dosyaya kaydedilmez; altyapı erişim logları metaveri tutabilir.

## 2A) Cloudflare Pages'e yükle

Pages projesinin kök dizini: `pages/`.

- Build output dizini: `public`.
- Functions: `pages/functions/api/build.js` (otomatik keşif; `public/` altına konulmaz).
- Pages proje ayarları -> Variables/Secrets:
  - `GSX_BUILD_ORIGIN` = `https://compiler.sizinalanadiniz.com` (sadece host, sonunda `/api/build` yok)
  - `GSX_BUILD_TOKEN` = backend'e koyduğunuz aynı gizli değer (secret)
- Production ve preview ortamlarında gerekli değerleri ayrı ayrı ayarlayın.
- Git ile deploy veya `cd pages && npx wrangler pages deploy public` kullanılabilir. Cloudflare dashboard'un **Direct Upload** arayüzüyle Functions'ın otomatik yüklenmesini varsaymayın; Functions için Git/CLI yolunu tercih edin.

## 2B) Cloudflare Worker'a yükle

**Alternatif** olarak, Pages yerine:

```sh
cd worker
npx wrangler secret put GSX_BUILD_TOKEN
npx wrangler deploy
```

Aynı Cloudflare Worker için `GSX_BUILD_ORIGIN` değişkenini Cloudflare panelinden tanımlayın (`https://compiler.sizinalanadiniz.com`). `GSX_BUILD_TOKEN`, backend tokeni ile aynı olmalıdır. `worker/wrangler.toml` dosyası `assets/` dizininden sadece statik UI'ı sunar. `worker.js` içinde Lua kaynak kodu yer almaz. `worker/assets/` altına diğer kaynak klasörlerini eklemeyin.

## 3) Koruma ve kontroller

- Tarayıcıdaki **Wasmoon, WASM, derleyici Lua modülleri, `compiler-worker.js` kaldırıldı**; artık statik endpointlerde yoklar.
- `/api/build`: sadece JSON POST; aynı-origin ve Fetch Metadata kontrolleri; 10 MiB Lua kaynak ve 32 MiB JSON taşıma sınırı.
- Özel backend: 32+ karakter Bearer token zorunlu; `strong` + `compact VM`, flatten, opaque, selfmod, antidebug, integrity sunucu tarafından zorunlu; build seed özel sunucu tarafından kriptografik rastgele üretilir.
- Kaynak `.lua`, `.luau`, `.txt` UI tarafından okunur ve **derleme amacıyla özel sunucuya gönderilir**. Kullanıcıya aksi söylenmez; local-only gizlilik özelliği artık yoktur.
- `/api/build` herkese açık sitede internete açık bir API'dir. **Origin kontrolü kimlik doğrulama değildir.** Kimin derleme yapabildiğini sınırlandırmak istiyorsanız **Cloudflare Access** (site ve API için) ve WAF/rate limits kullanın. Sadece statik dosya gizleme ile ücretli/yetkili erişim kurulamaz.
- Bearer token değerini `ui-src`, `pages/public`, `worker/assets`, Wrangler dosyası veya Git geçmişinde tutmayın. Yetkisiz erişim şüphesi varsa tokeni değiştirin.
- Eski dağıtımda `public/compiler-worker.js` veya 1.9 MB `index.html` halen CDN'de duruyorsa **eski deploy'u silin ve Cloudflare cache'ini temizleyin**. Yeni dosyalar eski kopyaları internetteki arşivlerden silemez.
- Çıktının kendisi Lua tarafında tersine mühendislikten tamamen korunamaz. Obfuscation, kriptografik gizlilik garantisi vermez.

## 4) Yerel test

```sh
python tools/build_public.py
python -m unittest discover -s tests -v
node tests/test_edge.mjs
python -m py_compile private-backend/web/service.py private-backend/web/compile_job.py
```

**Test durumu:** statik sızıntı, HTML içi JS syntax, Pages API/Worker route testleri ve Python syntax testleri yapıldı. Bu çalışma ortamında `lupa` kurulu olmadığı ve ağ erişimiyle yüklenemediği için **gerçek Lua derleme ve canlı Cloudflare deployment end-to-end çalıştırılamadı**. Backend'i kurduktan sonra `.lua` ve `.luau` ile canlı deneme yapın.

## Dosyanın asıl düzeltmesi

Önce: `index.html` ~1.968.000 bayt ve içinde Lua VM/derleyici kaynakları, WASM, modüller.

Sonra: `index.html` ~154.000 bayt (sadece UI; tam boy yeniden üretimde boyut değişebilir), **derleyici kodu gönderilmiyor**. Site hâlâ HTML döndürür; aksi halde normal tarayıcı arayüzü gösterilemez.
