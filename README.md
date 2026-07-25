# Discord self-message cleaner (Windows)

Edits each of **your own** messages once, then deletes it, in the channels and
DMs you choose. It only touches messages authored by the account whose token
you provide.

> **Warning:** Automating a *user* account ("self-botting") violates Discord's
> Terms of Service and can get your account banned. Use at your own risk. The
> built-in delays and dry-run mode are there to keep you safe — don't remove
> them or crank the speed.

---

## 1. Install

1. Install **Python 3.8+** from https://www.python.org/downloads/
   (tick **"Add Python to PATH"** during install).
2. Open **Command Prompt** and run:
   ```
   pip install requests
   ```

## 2. Get your info

Turn on **Developer Mode** first:
**Discord → Settings → Advanced → Developer Mode → ON**

- **Your user ID:** click your avatar (bottom-left) → **Copy User ID**.
- **A server channel ID:** right-click the channel name → **Copy Channel ID**.
- **A DM channel ID:** open the DM, then either right-click it in the left list
  → **Copy Channel ID**, or read it from the URL —
  `discord.com/channels/@me/<THIS_NUMBER>`.
- **Your token:** open Discord in a **web browser**, press `F12` →
  **Network** tab → click any request to `discord.com/api/...` → find the
  **`Authorization`** request header. That value is your token.
  **Never share this token with anyone — it's full access to your account.**

## 3. Configure

Open `config.json` and fill in:

| Field          | What it is                                                        |
|----------------|-------------------------------------------------------------------|
| `token`        | Your user token (from step 2).                                    |
| `user_id`      | Your user ID.                                                     |
| `edit_text`    | What each message is edited to before deletion (default `"."`).  |
| `dry_run`      | `true` = preview only; `false` = actually edit + delete.         |
| `edit_delay`   | Seconds to wait after each edit.                                 |
| `delete_delay` | Seconds to wait after each delete.                              |
| `read_delay`   | Seconds between fetching pages of messages.                      |
| `channel_ids`  | List of server channel IDs to clean.                            |
| `dm_ids`       | List of DM channel IDs to clean.                                 |

Put `config.json` in the **same folder** as `deleter.py`.

## 4. Run

From that folder in Command Prompt:

```
python deleter.py
```

- First run with `"dry_run": true` — it lists every message it *would* touch.
- When you're happy, set `"dry_run": false`, run again, and type `DELETE`
  when prompted.

## Notes

- It processes messages newest → oldest and pages through your whole history in
  each listed channel.
- If a channel returns 403/404 it's skipped (you left it, no access, etc.).
- If your token stops working (401), log out/in on the web to refresh it.
- Keep the delays around 1s. Going faster mostly just triggers rate limits
  (which it waits out anyway) and raises your ban risk.
