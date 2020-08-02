import React from 'react'
import { MenuItem } from '../../models'
import styles from './headerMenu.module.css'
import HeaderMenuItem from '../HeaderMenuItem'
import HeaderMenuExpandableItem from '../HeaderMenuExpandableItem'

interface HeaderMenuProps {
    itemList: MenuItem[]
}

const HeaderMenu = (props: HeaderMenuProps) => {

    var itemList = props.itemList.filter((item) =>!((!item.label || item.label ==='') && !item.iconComp && !item.iconName && !item.customComp))

    return (
        <div className={styles.headerMenuContainer}>
            {itemList.map((item) => {
                return (
                    <div className={styles.headerMenuItemContainer}>
                        {item.customComp ? (
                            item.customComp
                        ) : item.subMenuItemList ? (
                            <HeaderMenuExpandableItem 
                                label={item.label}
                                iconComp={item.iconComp}
                                iconName = {item.iconName}
                                subMenuItemList = {item.subMenuItemList}
                            />
                        ) : (
                            <HeaderMenuItem
                                onClick={() => {
                                    if (item.onClick) item.onClick()
                                }}
                                label={item.label}
                                iconComp ={item.iconComp}
                                iconName={item.iconName}                                
                            />
                        )}
                    </div>
                )
            })}
        </div>
    )
}

export default HeaderMenu
